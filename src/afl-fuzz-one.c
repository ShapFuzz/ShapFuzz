/*
   american fuzzy lop++ - fuzze_one routines in different flavours
   ---------------------------------------------------------------

   Originally written by Michal Zalewski

   Now maintained by Marc Heuse <mh@mh-sec.de>,
                        Heiko Eißfeldt <heiko.eissfeldt@hexco.de> and
                        Andrea Fioraldi <andreafioraldi@gmail.com>

   Copyright 2016, 2017 Google Inc. All rights reserved.
   Copyright 2019-2022 AFLplusplus Project. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     https://www.apache.org/licenses/LICENSE-2.0

   This is the real deal: the program takes an instrumented binary and
   attempts a variety of basic fuzzing tricks, paying close attention to
   how they affect the execution path.

 */

#include "afl-fuzz.h"
#include <string.h>
#include <limits.h>
#include "cmplog.h"
#include <float.h>

/* MOpt */

static int select_algorithm(afl_state_t *afl, u32 max_algorithm) {

  int i_puppet, j_puppet = 0, operator_number = max_algorithm;

  double range_sele =
      (double)afl->probability_now[afl->swarm_now][operator_number - 1];
  double sele = ((double)(rand_below(afl, 10000) * 0.0001 * range_sele));

  for (i_puppet = 0; i_puppet < operator_num; ++i_puppet) {

    if (unlikely(i_puppet == 0)) {

      if (sele < afl->probability_now[afl->swarm_now][i_puppet]) { break; }

    } else {

      if (sele < afl->probability_now[afl->swarm_now][i_puppet]) {

        j_puppet = 1;
        break;

      }

    }

  }

  if ((j_puppet == 1 &&
       sele < afl->probability_now[afl->swarm_now][i_puppet - 1]) ||
      (i_puppet + 1 < operator_num &&
       sele > afl->probability_now[afl->swarm_now][i_puppet + 1])) {

    FATAL("error select_algorithm");

  }

  return i_puppet;

}

/* Helper to choose random block len for block operations in fuzz_one().
   Doesn't return zero, provided that max_len is > 0. */

static inline u32 choose_block_len(afl_state_t *afl, u32 limit) {

  u32 min_value, max_value;
  u32 rlim = MIN(afl->queue_cycle, (u32)3);

  if (unlikely(!afl->run_over10m)) { rlim = 1; }

  switch (rand_below(afl, rlim)) {

    case 0:
      min_value = 1;
      max_value = HAVOC_BLK_SMALL;
      break;

    case 1:
      min_value = HAVOC_BLK_SMALL;
      max_value = HAVOC_BLK_MEDIUM;
      break;

    default:

      if (likely(rand_below(afl, 10))) {

        min_value = HAVOC_BLK_MEDIUM;
        max_value = HAVOC_BLK_LARGE;

      } else {

        min_value = HAVOC_BLK_LARGE;
        max_value = HAVOC_BLK_XL;

      }

  }

  if (min_value >= limit) { min_value = 1; }

  return min_value + rand_below(afl, MIN(max_value, limit) - min_value + 1);

}

/* Helper function to see if a particular change (xor_val = old ^ new) could
   be a product of deterministic bit flips with the lengths and stepovers
   attempted by afl-fuzz. This is used to avoid dupes in some of the
   deterministic fuzzing operations that follow bit flips. We also
   return 1 if xor_val is zero, which implies that the old and attempted new
   values are identical and the exec would be a waste of time. */

static u8 could_be_bitflip(u32 xor_val) {

  u32 sh = 0;

  if (!xor_val) { return 1; }

  /* Shift left until first bit set. */

  while (!(xor_val & 1)) {

    ++sh;
    xor_val >>= 1;

  }

  /* 1-, 2-, and 4-bit patterns are OK anywhere. */

  if (xor_val == 1 || xor_val == 3 || xor_val == 15) { return 1; }

  /* 8-, 16-, and 32-bit patterns are OK only if shift factor is
     divisible by 8, since that's the stepover for these ops. */

  if (sh & 7) { return 0; }

  if (xor_val == 0xff || xor_val == 0xffff || xor_val == 0xffffffff) {

    return 1;

  }

  return 0;

}

/* Helper function to see if a particular value is reachable through
   arithmetic operations. Used for similar purposes. */

static u8 could_be_arith(u32 old_val, u32 new_val, u8 blen) {

  u32 i, ov = 0, nv = 0, diffs = 0;

  if (old_val == new_val) { return 1; }

  /* See if one-byte adjustments to any byte could produce this result. */

  for (i = 0; (u8)i < blen; ++i) {

    u8 a = old_val >> (8 * i), b = new_val >> (8 * i);

    if (a != b) {

      ++diffs;
      ov = a;
      nv = b;

    }

  }

  /* If only one byte differs and the values are within range, return 1. */

  if (diffs == 1) {

    if ((u8)(ov - nv) <= ARITH_MAX || (u8)(nv - ov) <= ARITH_MAX) { return 1; }

  }

  if (blen == 1) { return 0; }

  /* See if two-byte adjustments to any byte would produce this result. */

  diffs = 0;

  for (i = 0; (u8)i < blen / 2; ++i) {

    u16 a = old_val >> (16 * i), b = new_val >> (16 * i);

    if (a != b) {

      ++diffs;
      ov = a;
      nv = b;

    }

  }

  /* If only one word differs and the values are within range, return 1. */

  if (diffs == 1) {

    if ((u16)(ov - nv) <= ARITH_MAX || (u16)(nv - ov) <= ARITH_MAX) {

      return 1;

    }

    ov = SWAP16(ov);
    nv = SWAP16(nv);

    if ((u16)(ov - nv) <= ARITH_MAX || (u16)(nv - ov) <= ARITH_MAX) {

      return 1;

    }

  }

  /* Finally, let's do the same thing for dwords. */

  if (blen == 4) {

    if ((u32)(old_val - new_val) <= ARITH_MAX ||
        (u32)(new_val - old_val) <= ARITH_MAX) {

      return 1;

    }

    new_val = SWAP32(new_val);
    old_val = SWAP32(old_val);

    if ((u32)(old_val - new_val) <= ARITH_MAX ||
        (u32)(new_val - old_val) <= ARITH_MAX) {

      return 1;

    }

  }

  return 0;

}

/* Last but not least, a similar helper to see if insertion of an
   interesting integer is redundant given the insertions done for
   shorter blen. The last param (check_le) is set if the caller
   already executed LE insertion for current blen and wants to see
   if BE variant passed in new_val is unique. */

static u8 could_be_interest(u32 old_val, u32 new_val, u8 blen, u8 check_le) {

  u32 i, j;

  if (old_val == new_val) { return 1; }

  /* See if one-byte insertions from interesting_8 over old_val could
     produce new_val. */

  for (i = 0; i < blen; ++i) {

    for (j = 0; j < sizeof(interesting_8); ++j) {

      u32 tval =
          (old_val & ~(0xff << (i * 8))) | (((u8)interesting_8[j]) << (i * 8));

      if (new_val == tval) { return 1; }

    }

  }

  /* Bail out unless we're also asked to examine two-byte LE insertions
     as a preparation for BE attempts. */

  if (blen == 2 && !check_le) { return 0; }

  /* See if two-byte insertions over old_val could give us new_val. */

  for (i = 0; (u8)i < blen - 1; ++i) {

    for (j = 0; j < sizeof(interesting_16) / 2; ++j) {

      u32 tval = (old_val & ~(0xffff << (i * 8))) |
                 (((u16)interesting_16[j]) << (i * 8));

      if (new_val == tval) { return 1; }

      /* Continue here only if blen > 2. */

      if (blen > 2) {

        tval = (old_val & ~(0xffff << (i * 8))) |
               (SWAP16(interesting_16[j]) << (i * 8));

        if (new_val == tval) { return 1; }

      }

    }

  }

  if (blen == 4 && check_le) {

    /* See if four-byte insertions could produce the same result
       (LE only). */

    for (j = 0; j < sizeof(interesting_32) / 4; ++j) {

      if (new_val == (u32)interesting_32[j]) { return 1; }

    }

  }

  return 0;

}

#ifndef IGNORE_FINDS

/* Helper function to compare buffers; returns first and last differing offset.
   We use this to find reasonable locations for splicing two files. */

static void locate_diffs(u8 *ptr1, u8 *ptr2, u32 len, s32 *first, s32 *last) {

  s32 f_loc = -1;
  s32 l_loc = -1;
  u32 pos;

  for (pos = 0; pos < len; ++pos) {

    if (*(ptr1++) != *(ptr2++)) {

      if (f_loc == -1) { f_loc = pos; }
      l_loc = pos;

    }

  }

  *first = f_loc;
  *last = l_loc;

  return;

}

#endif                                                     /* !IGNORE_FINDS */

u8 whether_satified(afl_state_t * afl){
  for(u32 i = 0;i < afl->new_edges_found_idx;i++){
    u32 cur_edge = afl->new_edges_found[i];
    if(!(afl->fsrv.trace_bits)[cur_edge]){
      return 0;
    } 
  }
  return 1;
}

// void show_mutated_pos(afl_state_t * afl){
//   printf("fn:%s\n", afl->queue_cur->ancestor_seed->fname);
//   printf("sum:%d(%u)\n", afl->queue_cur->ancestor_seed->mutated_pos_num, afl->queue_cur->ancestor_seed->len);
//   for(u32 i = 0;i < afl->queue_cur->ancestor_seed->len;i++){
//     if(afl->queue_cur->ancestor_seed->mutated_pos[i].flag >= 1){
//       printf("%d ", i);
//     }
//   }
//   printf("\n");
// }

void stat_analysis(afl_state_t * afl, s32 temp_len, u8 *out_buf, u8 *in_buf, s32 len, u8 history_mode){

  if(afl->record_flag && afl->tmp_mutated_pos_idx != 0){
    double average_reward;
    if(afl->queue_cur->n_fuzz_entry != afl->cur_n_fuzz_idx){
      average_reward = (1 - (double)((double)afl->n_fuzz[afl->cur_n_fuzz_idx] / (double)afl->fsrv.total_execs))/(afl->tmp_mutated_pos_idx * afl->tmp_mutated_pos_idx);
    } 
    else{
      average_reward = 0;
    }

    for(u32 i = 0; i < afl->tmp_mutated_pos_idx;i++){
      u32 target_pos = afl->tmp_mutated_pos[i];
      afl->dataset_reward[target_pos] += average_reward;
      afl->hit_nums[target_pos]++;
      afl->dataset_size++;

      afl->tmp_mutated_pos_flag[target_pos] = 0;
      afl->tmp_mutated_pos[i] = 0;
    }
    if(afl->tmp_mutated_pos_idx == 0) exit(0);
    afl->tmp_mutated_pos_idx = 0;
  }

  if(afl->read_flag == 1){
    printf("do not exec has_new_bits in this round\n");
    afl->mini_mode = 0;
    return;
  }

  afl->read_flag = 1;
  afl->mini_mode = 1;

  

  if(afl->new_edges_found_idx == 0 || afl->queue_cur->ancestor_seed == NULL || afl->use_splice_mutator || afl->from_splicing){
    afl->mini_mode = 0;    
    u32 after = count_non_255_bytes(afl, afl->virgin_bits);
    afl->queue_cur->found_edges += (after - afl->before);
    afl->before = after;

    if(afl->queue_cur->splice == 1 && afl->queue_cur->found_edges > 8 && afl->queue_cur->len > 512){
      struct queue_entry* q = afl->queue_cur;

      u32 map_size = afl->fsrv.map_size;
      q->virgin_bits = ck_alloc(map_size);
      memset(q->virgin_bits, 255, map_size);

      q->reset_times = ck_alloc(map_size);
      memset(q->reset_times, 0, map_size);

      q->initial_seed = 1;
      q->ancestor_seed = q;
      q->splice = 0;
      q->incre = 1;
      q->map = (u64 *)malloc(sizeof(u64) * q->len);
      for(u32 i = 0;i < q->len;i++) (q->map)[i] = i;

      q->mutated_pos = (struct arm *)malloc(sizeof(struct arm) * q->len);
      for(u32 i = 0;i < q->len;i++){
        q->mutated_pos[i].flag = 0;
        q->mutated_pos[i].A = NULL;
        q->mutated_pos[i].b = NULL;
      }
      q->mutated_pos_num = 0;
    }
    return;
  } 
  temp_len = len;

  if(afl->new_edges_found_idx > 1000){
    printf("There may be existing some problems\n");
    return;
  }
  u8 correctness = 0;
  float changed_num = 0;
  for(int i = 0;i < temp_len;i++){
    if(out_buf[i] == in_buf[i]) continue;
    changed_num++;
  }

  float necessary_nums = 0;
  for(int i = 0;i < temp_len;i++){
    if(out_buf[i] == in_buf[i]) continue;

    u8 tmp = out_buf[i];
    out_buf[i] = in_buf[i];
    common_fuzz_stuff(afl, out_buf, temp_len);

    if(whether_satified(afl) == 0){
      necessary_nums++;
      correctness = 1;
      out_buf[i] = tmp;
      u32 ii = (afl->queue_cur->map)[i];

      if(ii > 1000000 || ii >= afl->queue_cur->ancestor_seed->len){
        exit(0);
      } 
      
      if(afl->queue_cur->ancestor_seed->mutated_pos[ii].flag < 1){
        afl->queue_cur->ancestor_seed->mutated_pos[ii].flag += 1;
        if(afl->queue_cur->ancestor_seed->mutated_pos[ii].flag >= 1){
          afl->queue_cur->ancestor_seed->mutated_pos[ii].A = M_I(afl->centers_num);
          afl->queue_cur->ancestor_seed->mutated_pos[ii].b = M_Zeros(afl->centers_num,1);
          afl->queue_cur->ancestor_seed->mutated_pos_num++;
        }
      }
      afl->queue_cur->ancestor_seed->mutated_pos[ii].add = 1;
    }
  }

  /*
    In theory, we should compare the current seed with the initial seed to obtain mutated positions. 
    However, in our experiments, we found that this would lead to certain early mutated positions being assigned disproportionately high weights.
    Therefore, we pay more attention to the latest mutated positions, believing that these bytes are more effective in subsequent mutations. 
    Thus, we only consider the latest mutated positions to calculate the \phi of these mutated positions and use them to update the Shapley values.
  */
  for(u32 i = 0;i < afl->queue_cur->ancestor_seed->len;i++){
    if(afl->queue_cur->ancestor_seed->mutated_pos[i].add == 1){
      // afl->queue_cur->ancestor_seed->mutated_pos[i].SV = (float)afl->new_edges_found_idx/necessary_nums;
      afl->queue_cur->ancestor_seed->mutated_pos[i].SV += (float)afl->new_edges_found_idx/necessary_nums;
      afl->queue_cur->ancestor_seed->mutated_pos[i].add = 0;
    }
  }

  afl->mini_mode = 0;
}


void update(afl_state_t *afl, u32 target_pos){
  if(afl->tmp_mutated_pos_flag[target_pos] == 0){
    afl->tmp_mutated_pos_flag[target_pos] = 1;
    afl->tmp_mutated_pos[afl->tmp_mutated_pos_idx] = target_pos;
    afl->tmp_mutated_pos_idx++;
  }
}

/*
  *Update log*
  - time: 2023.7.15
  - description: 
    To address potential issues stemming from "The Impact of Self-New Edges" and "Semantic Consistency Within Families," we've made updates to the usage of CMAB: 
    (1) We set the reward as the rarity of the path exercised by the mutated input. 
    (2) We've updated the calculation formula for Score(s, p)
*/
u32 select_position_based_on_distribution(afl_state_t *afl){
  if(afl->distribution_sum == 0 && afl->history_mutation_sequence_idx){
    afl->distribution_analyzed++;

    double tmp = 0;
    for(u32 i = 0;i < afl->history_mutation_sequence_idx;i++){
      u32 cur_pos = afl->history_mutation_sequence[i];

      struct queue_entry * ancestor_node = afl->queue_cur->ancestor_seed;
      u32 ii = (afl->queue_cur->map)[cur_pos];
      double result;
      if(ancestor_node->mutated_pos[ii].flag >= 1){
        Matrix* feature_vec_copy = Matrix_copy(afl->queue_cur->feature_vec);
        Matrix* A_copy = Matrix_copy(ancestor_node->mutated_pos[ii].A);
        Matrix* b_copy = Matrix_copy(ancestor_node->mutated_pos[ii].b);

        Matrix* A_Inverse = M_Inverse(A_copy);
        Matrix* theta = M_mul(A_Inverse,b_copy);
        Matrix* theta_T = M_T(theta);
        Matrix* r1 = M_mul(theta_T,feature_vec_copy);

        Matrix* feature_vec_T = M_T(feature_vec_copy);
        Matrix* m1 = M_mul(feature_vec_T,A_Inverse);
        Matrix* m2 = M_mul(m1,feature_vec_copy);
        double m3 = 0.5 * sqrt(m2->data[0]);
        result = r1->data[0] + m3 + ancestor_node->mutated_pos[ii].SV;

        if(m2->data[0] < 0 || isnan(result)){
          printf("feature_vec_copy\n");
          M_print(feature_vec_copy);
          printf("A_copy\n");
          M_print(A_copy);
          printf("b_copy\n");
          M_print(b_copy);

          printf("A_Inverse\n");
          M_print(A_Inverse);
          printf("theta\n");
          M_print(theta);
          printf("theta_T\n");
          M_print(theta_T);
          printf("r1\n");
          M_print(r1);

          printf("feature_vec_T\n");
          M_print(feature_vec_T);
          printf("m1\n");
          M_print(m1);
          printf("m2\n");
          M_print(m2);
          
          printf("m3:%lf\n", m3);
          printf("result:%lf\n", result);
          exit(0);
        }

        M_free(A_Inverse);
        M_free(theta);
        M_free(theta_T);
        M_free(r1);
        M_free(feature_vec_T);
        M_free(m1);
        M_free(m2);

        M_free(feature_vec_copy);
        M_free(A_copy);
        M_free(b_copy);

      }else{
        result = 0;
      }

      if(result < 0) result = 0.05;
      tmp += result;
      afl->distribution[i] = tmp;
    }
    afl->distribution_sum = tmp;
  }

  if(afl->distribution_sum){
    double choose = ((double)rand()/RAND_MAX) * afl->distribution_sum;
    for(u32 i = 0;i < afl->history_mutation_sequence_idx;i++){
      if(afl->distribution[i] >= choose){
        return afl->history_mutation_sequence[i];
      }
    }

    // for(u32 i = 0;i < afl->history_mutation_sequence_idx;i++){
    //   printf("%u:%u -> %f\n", i, afl->history_mutation_sequence[i], afl->distribution[i]);
    // }
    return afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
  }else{
    return afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
  }
  
}

void generate_mutation_sequence(afl_state_t *afl){
  afl->history_mutation_sequence_idx = 0;
  for(u32 i = 0;i < afl->queue_cur->len;i++){
    u64 ii = (afl->queue_cur->map)[i];
    if(ii > 1000000 || ii >= afl->queue_cur->ancestor_seed->len){
      exit(0);
    } 
    if(afl->queue_cur->ancestor_seed->mutated_pos[ii].flag >= 1){
      afl->history_mutation_sequence[afl->history_mutation_sequence_idx] = i;
      afl->history_mutation_sequence_idx++;
    }
  }
}

void generate_mutation_sequence_new_mode(afl_state_t *afl){
  afl->new_mutation_sequence_idx = 0;
  for(u32 i = 0; i < afl->queue_cur->related_num;i++){
    afl->new_mutation_sequence[afl->new_mutation_sequence_idx] = (afl->queue_cur->related_bytes)[i];
    afl->new_mutation_sequence_idx++;
  }
}


/* [INFORMATION]
    MATRIX_HUB
    AUTHOR: Xiping.Yu
    E-MAIL:Amoiensis@outlook.com
    GITHUB: https://github.com/Amoiensis/Matrix_hub
    DATE: 2020.02.12-2022.05.28
    VERSION: 1.5.1
    CASE: Matrix Operation (C)
    DETAILS: The demo-code for Matrix_Hub.
    LICENSE: Apache-2.0
*/



int help(char *file_name) {
    printf(">>HELP(");
    printf(file_name);
    printf(")\n");
    char temp_route[_MAX_HELP_LENGTH_] = "./help/";
    char temp_txt[5] = ".txt";
    strcat(temp_route, file_name);
    strcat(temp_route, temp_txt);
    FILE *fp;
    char ch;
    fp = fopen(temp_route, "r");
    if (fp == NULL) {
        printf(temp_route);
        printf(" can not open!\n");
    } else {
        fscanf(fp, "%c", &ch);
        while (!feof(fp)) {
            putchar(ch);
            fscanf(fp, "%c", &ch);
        }
        fclose(fp);
    }
    printf("\n");
}

Matrix *Matrix_gen(int row, int column, MATRIX_TYPE *data) {
    Matrix *_mat = (Matrix *) malloc(sizeof(Matrix));
    _mat->row = row;
    _mat->column = column;
    int size = _mat->row * _mat->column;
    _mat->data = (MATRIX_TYPE *) malloc((size) * sizeof(MATRIX_TYPE));
    int i;
    for (i = 0; i < size; i++) {
        _mat->data[i] = data[i];
    }
    return _mat;
}

Matrix *Matrix_copy(Matrix *_mat_sourse) {
    Matrix *_mat_copy = Matrix_gen(_mat_sourse->row, _mat_sourse->column, _mat_sourse->data);
    return _mat_copy;
}

Matrix *M_add_sub(MATRIX_TYPE scale_mat_subed, Matrix *_mat_subed, MATRIX_TYPE scale_mat_minus, Matrix *_mat_minus) {
    Matrix *_mat_result = NULL;
    if ((_mat_subed->column == _mat_minus->column) && (_mat_subed->row == _mat_minus->row)) {
        _mat_result = Matrix_copy(_mat_subed);
        int size = (_mat_subed->row) * (_mat_subed->column), i;
        for (i = 0; i < size; i++) {
            _mat_result->data[i] = (_mat_result->data[i]) * scale_mat_subed - (_mat_minus->data[i]) * scale_mat_minus;
        }
    } else {
        printf(M_add_sub_003);
    }
    return _mat_result;
}

Matrix *M_mul(Matrix *_mat_left, Matrix *_mat_right) {
    (_DETAILED_>=3)?printf(">>Matrix_%x * Matrix_%x =\n", _mat_left, _mat_right):0;
    Matrix *_mat_result = NULL;
    if (_mat_left->column != _mat_right->row) {
        printf(M_mul_001);
    } else {
        _mat_result = (Matrix *) malloc(sizeof(Matrix));
        int row = _mat_left->row;
        int mid = _mat_left->column;
        int column = _mat_right->column;
        int i, j, k;
        MATRIX_TYPE *_data = (MATRIX_TYPE *) malloc((row * column) * sizeof(MATRIX_TYPE));
        MATRIX_TYPE temp = 0;
        /*Ergodic*/
        for (i = 0; i < row; i++) {
            for (j = 0; j < column; j++) {
                /*Caculate Element*/
                temp = 0;
                for (k = 0; k < mid; k++) {
                    temp += (_mat_left->data[i * mid + k]) * (_mat_right->data[k * column + j]);
                }
                _data[i * column + j] = temp;
            }
        }
        _mat_result->row = row;
        _mat_result->column = column;
        _mat_result->data = _data;
    }
    (_DETAILED_>=3)?printf("\tMatrix_%x\n", _mat_result):0;
    return _mat_result;
}

int M_print(Matrix *_mat) {
    printf(">>Matrix_%x:\n", _mat);
    int i, j;
    for (i = 0; i < _mat->row; i++) {
        for (j = 0; j < _mat->column; j++) {
            printf(PRECISION, _mat->data[i * (_mat->column) + j]);
        }
        printf("\n");
    }
    return 0;
}

Matrix *M_I(int order) {
    Matrix *I_mat = (Matrix *) malloc(sizeof(Matrix));
    I_mat->column = order;
    I_mat->row = order;
    int size = order * order, i;
    MATRIX_TYPE *data = (MATRIX_TYPE *) malloc((size) * sizeof(MATRIX_TYPE));
    for (i = 0; i < size; i++) {
        data[i] = 0;
    }
    for (i = 0; i < order; i++) {
        data[i * (order + 1)] = 1;
    }
    I_mat->data = data;
    return I_mat;
}

int M_E_trans(Matrix *_mat, Etrans_struct *_Etrans_, int line_setting) {
    int line_num, i;
    if (line_setting == _ROW_) {
        line_num = _mat->column;
        if (_Etrans_->scale) {
            for (i = 0; i < line_num; i++) {
                _mat->data[(_Etrans_->minuend_line - 1) * (_mat->column) + i] -=
                        (_Etrans_->scale) * (_mat->data[(_Etrans_->subtractor_line - 1) * (_mat->column) + i]);

            }
        } else {
            if ((_Etrans_->minuend_line < 0) && (_Etrans_->subtractor_line < 0)) {
                M_Swap(_mat, -(_Etrans_->minuend_line), -(_Etrans_->subtractor_line), line_setting);
            }
        }
    } else {
        line_num = _mat->row;
        if (_Etrans_->scale) {
            for (i = 0; i < line_num; i++) {
                _mat->data[(_Etrans_->minuend_line - 1) + (_mat->column) * i] -=
                        (_Etrans_->scale) * (_mat->data[(_Etrans_->subtractor_line - 1) + (_mat->column) * i]);
            }
        } else {
            if ((_Etrans_->minuend_line < 0) && (_Etrans_->subtractor_line < 0)) {
                M_Swap(_mat, -(_Etrans_->minuend_line), -(_Etrans_->subtractor_line), line_setting);
            }
        }
    }
    return 0;
}

Matrix *Etrans_4_Inverse(Matrix *_mat_result, Etrans_struct *_Etrans_, int line_setting) {
    Etrans_struct *temp_Etrans = _Etrans_, *temp_Etrans_pre = _Etrans_;
    int temp_num = 0;
    while (temp_Etrans != NULL) {
        temp_num = temp_Etrans->minuend_line;
        temp_Etrans->minuend_line = temp_Etrans->subtractor_line;
        temp_Etrans->subtractor_line = temp_num;
        M_E_trans(_mat_result, temp_Etrans, line_setting);
        temp_Etrans = temp_Etrans->forward_E_trans;
        free(temp_Etrans_pre);
        temp_Etrans_pre = temp_Etrans;
    }
    return _mat_result;
}

Matrix *Etrans_2_Matrix(Etrans_struct *_Etrans_, int order, int line_setting) {
    Etrans_struct *temp_Etrans = _Etrans_;
    Matrix *_mat_result = M_I(order);
    if (_Etrans_ != NULL) {
        while ((temp_Etrans->next_E_trans) != NULL) {
            temp_Etrans = temp_Etrans->next_E_trans;
        }
        do {
            temp_Etrans->scale = (-1) * temp_Etrans->scale;
            M_E_trans(_mat_result, temp_Etrans, line_setting);
            temp_Etrans->scale = (-1) * temp_Etrans->scale;
            temp_Etrans = temp_Etrans->forward_E_trans;
            if (temp_Etrans != NULL) {
                free(temp_Etrans->next_E_trans);
            }
        } while (temp_Etrans != NULL);
    }
    return _mat_result;
}

Uptri_struct *M_Uptri_(Matrix *_mat_source) {
    Matrix *_mat = Matrix_copy(_mat_source);
    int i, j, k, flag;
    Etrans_struct *_Etrans_temp_last = NULL;
    Etrans_struct *_Etrans_temp_head = NULL;

    for (i = 0; i < _mat->column; i++) {
        for (j = i + 1; j < _mat->row; j++) {
            flag = 0;
            Etrans_struct *_Etrans_temp = (Etrans_struct *) malloc(sizeof(Etrans_struct));
            _Etrans_temp->minuend_line = j + 1;
            _Etrans_temp->subtractor_line = i + 1;
            if ((_mat->data[(_mat->column) * i + i]) != 0) {
                _Etrans_temp->scale = (_mat->data[(_mat->column) * j + i]) / (_mat->data[(_mat->column) * i + i]);
            } else {
                _Etrans_temp->scale = 0;
                for (k = i + 1; k < _mat->row; k++) {
                    flag = 1;
                    if ((_mat->data[(_mat->column) * k + i]) != 0) {
                        _Etrans_temp->minuend_line = -(i + 1);
                        _Etrans_temp->subtractor_line = -(k + 1);
                        flag = 2;
                        break;
                    }
                }
                if (flag == 1) {
                    break;
                }
            }
            _Etrans_temp->forward_E_trans = NULL;
            _Etrans_temp->next_E_trans = NULL;
            if (_Etrans_temp_head == NULL) {
                _Etrans_temp_head = _Etrans_temp;
                _Etrans_temp->forward_E_trans = NULL;
            } else {
                _Etrans_temp->forward_E_trans = _Etrans_temp_last;

            }
            if ((i + 1) == _mat->column) {
                _Etrans_temp->next_E_trans = NULL;
            } else {
                if (_Etrans_temp_last != NULL) {
                    _Etrans_temp_last->next_E_trans = _Etrans_temp;
                }
            }
            M_E_trans(_mat, _Etrans_temp, _ROW_);
            _Etrans_temp_last = _Etrans_temp;

            if (flag == 2) {
                i = i - 1;
                break;
            }
        }
    }
    Matrix *trans_mat = Etrans_2_Matrix(_Etrans_temp_head, _mat->row, _ROW_);
    Uptri_struct *_Uptri = (Uptri_struct *) malloc(sizeof(Uptri_struct));
    _Uptri->trans_matrix = trans_mat;
    _Uptri->Uptri_matrix = _mat;
    (_DETAILED_>=1)?printf(">>Uptri(Matrix_%x)=\n", _mat_source):0;
    (_DETAILED_>=1)?printf("\tMatrix_%x * Matrix_%x\n", trans_mat, _mat):0;
    return _Uptri;
}

M_inv_struct *M_Uptri_4inv(Matrix *_mat_source) {
    Matrix *_mat = Matrix_copy(_mat_source);
    int i, j, k, flag;
    Etrans_struct *_Etrans_temp_last = NULL;
    Etrans_struct *_Etrans_temp_head = NULL;

    for (i = 0; i < _mat->column; i++) {
        for (j = i + 1; j < _mat->row; j++) {
            flag = 0;
            Etrans_struct *_Etrans_temp = (Etrans_struct *) malloc(sizeof(Etrans_struct));
            _Etrans_temp->minuend_line = j + 1;
            _Etrans_temp->subtractor_line = i + 1;
            if ((_mat->data[(_mat->column) * i + i]) != 0) {
                _Etrans_temp->scale = (_mat->data[(_mat->column) * j + i]) / (_mat->data[(_mat->column) * i + i]);
            } else {
                _Etrans_temp->scale = 0;
                for (k = i + 1; k < _mat->row; k++) {
                    flag = 1;
                    if ((_mat->data[(_mat->column) * k + i]) != 0) {
                        _Etrans_temp->minuend_line = -(i + 1);
                        _Etrans_temp->subtractor_line = -(k + 1);
                        flag = 2;
                        break;
                    }
                }
                if (flag == 1) {
                    break;
                }
            }
            _Etrans_temp->forward_E_trans = NULL;
            _Etrans_temp->next_E_trans = NULL;
            //if (j==1){
            if (_Etrans_temp_head == NULL) {
                _Etrans_temp_head = _Etrans_temp;
                _Etrans_temp->forward_E_trans = NULL;
            } else {
                _Etrans_temp->forward_E_trans = _Etrans_temp_last;

            }
            if ((i + 1) == _mat->column) {
                _Etrans_temp->next_E_trans = NULL;
            } else {
                if (_Etrans_temp_last != NULL) {
                    _Etrans_temp_last->next_E_trans = _Etrans_temp;
                }
            }
            M_E_trans(_mat, _Etrans_temp, _ROW_);
            _Etrans_temp_last = _Etrans_temp;

            if (flag == 2) {
                i = i - 1;
                break;
            }
        }
    }
    M_inv_struct *_Uptri = (M_inv_struct *) malloc(sizeof(M_inv_struct));
    _Uptri->_matrix = _mat;
    _Uptri->_Etrans_head = _Etrans_temp_last;
    return _Uptri;
}

Lowtri_struct *M_Lowtri_(Matrix *_mat_source) {
    Matrix *_mat = Matrix_copy(_mat_source);
    int i, j, k, flag;
    Etrans_struct *_Etrans_temp_last = NULL;
    Etrans_struct *_Etrans_temp_head = NULL;
    for (i = 0; i < _mat->row; i++) {
        for (j = i + 1; j < _mat->column; j++) {
            flag = 0;
            Etrans_struct *_Etrans_temp = (Etrans_struct *) malloc(sizeof(Etrans_struct));
            _Etrans_temp->minuend_line = j + 1;
            _Etrans_temp->subtractor_line = i + 1;


            if ((_mat->data[(_mat->column) * i + i]) != 0) {
                _Etrans_temp->scale = (_mat->data[(_mat->column) * i + j]) / (_mat->data[(_mat->column) * i + i]);
            } else {
                _Etrans_temp->scale = 0;
                for (k = i + 1; k < _mat->row; k++) {
                    flag = 1;
                    if ((_mat->data[(_mat->column) * k + i]) != 0) {
                        _Etrans_temp->minuend_line = -(i + 1);
                        _Etrans_temp->subtractor_line = -(k + 1);
                        flag = 2;
                        break;
                    }
                }
                if (flag == 1) {
                    break;
                }
            }

            _Etrans_temp->forward_E_trans = NULL;
            _Etrans_temp->next_E_trans = NULL;
            if (_Etrans_temp_head == NULL) {
                _Etrans_temp_head = _Etrans_temp;
                _Etrans_temp->forward_E_trans = NULL;
            } else {
                _Etrans_temp->forward_E_trans = _Etrans_temp_last;
            }
            if ((i + 1) == _mat->column) {
                _Etrans_temp->next_E_trans = NULL;
            } else {
                if (_Etrans_temp_last != NULL) {
                    _Etrans_temp_last->next_E_trans = _Etrans_temp;
                }
            }
            M_E_trans(_mat, _Etrans_temp, _COLUMN_);
            M_print(_mat); 
            _Etrans_temp_last = _Etrans_temp;
            if (flag == 2) {
                i = i - 1;
                break;
            }
        }
    }
    Matrix *trans_mat = Etrans_2_Matrix(_Etrans_temp_head, _mat->row, _COLUMN_);
    Lowtri_struct *_Lowtri = (Lowtri_struct *) malloc(sizeof(Lowtri_struct));
    _Lowtri->trans_matrix = trans_mat;
    _Lowtri->Lowtri_matrix = _mat;
    (_DETAILED_>=1)?printf(">>Lowtri(Matrix_%x)=\n", _mat_source):0;
    (_DETAILED_>=1)?printf("\tMatrix_%x * Matrix_%x\n", _mat, trans_mat):0;
    return _Lowtri;
}

M_inv_struct *M_Lowtri_4inv(Matrix *_mat_source) {
    Matrix *_mat = Matrix_copy(_mat_source);
    int i, j, k, flag;
    Etrans_struct *_Etrans_temp_last = NULL;
    Etrans_struct *_Etrans_temp_head = NULL;
    for (i = 0; i < _mat->row; i++) {
        for (j = i + 1; j < _mat->column; j++) {
            flag = 0;
            Etrans_struct *_Etrans_temp = (Etrans_struct *) malloc(sizeof(Etrans_struct));
            _Etrans_temp->minuend_line = j + 1;
            _Etrans_temp->subtractor_line = i + 1;


            if ((_mat->data[(_mat->column) * i + i]) != 0) {
                _Etrans_temp->scale = (_mat->data[(_mat->column) * i + j]) / (_mat->data[(_mat->column) * i + i]);
            } else {
                _Etrans_temp->scale = 0;
                for (k = i + 1; k < _mat->row; k++) {
                    flag = 1;
                    if ((_mat->data[(_mat->column) * k + i]) != 0) {
                        _Etrans_temp->minuend_line = -(i + 1);
                        _Etrans_temp->subtractor_line = -(k + 1);
                        flag = 2;
                        break;
                    }
                }
                if (flag == 1) {
                    break;
                }
            }

            _Etrans_temp->forward_E_trans = NULL;
            _Etrans_temp->next_E_trans = NULL;
            if (_Etrans_temp_head == NULL) {
                _Etrans_temp_head = _Etrans_temp;
                _Etrans_temp->forward_E_trans = NULL;
            } else {
                _Etrans_temp->forward_E_trans = _Etrans_temp_last;
            }
            if ((i + 1) == _mat->column) {
                _Etrans_temp->next_E_trans = NULL;
            } else {
                if (_Etrans_temp_last != NULL) {
                    _Etrans_temp_last->next_E_trans = _Etrans_temp;
                }
            }
            M_E_trans(_mat, _Etrans_temp, _COLUMN_);
            _Etrans_temp_last = _Etrans_temp;
            if (flag == 2) {
                i = i - 1;
                break;
            }
        }
    }
    M_inv_struct *_Lowtri = (M_inv_struct *) malloc(sizeof(M_inv_struct));
    _Lowtri->_matrix = _mat;
    _Lowtri->_Etrans_head = _Etrans_temp_last;
    return _Lowtri;
}

Matrix *M_Dia_Inv(Matrix *_mat_source) {
    Matrix *_mat_inv = NULL;
    if (_mat_source->row != _mat_source->column) {
        printf(M_Dia_Inv_002);
        system("pause");
    } else {
        _mat_inv = Matrix_copy(_mat_source);
        MATRIX_TYPE *data = _mat_inv->data;
        int i, order = _mat_source->column;
        for (i = 0; i < order; i++) {
            if((data)[i * (order + 1)] == 0){
                printf(M_Dia_Inv_023);
                system("pause");
                (data)[i * (order + 1)] = 1 / (data[i * (order + 1)]);
            }else{
                (data)[i * (order + 1)] = 1 / (data[i * (order + 1)]);
            }
        }
    }
    return _mat_inv;
}


Matrix *M_Inverse(Matrix *_mat) {
    M_inv_struct *_Uptri_ = M_Uptri_4inv(_mat);
    M_inv_struct *_Lowtri_ = M_Lowtri_4inv(_Uptri_->_matrix);
    Matrix *_mat_dia_inv = M_Dia_Inv(_Lowtri_->_matrix);
    Matrix *_mat_inv = Etrans_4_Inverse(_mat_dia_inv, _Lowtri_->_Etrans_head, _ROW_);
    _mat_inv = Etrans_4_Inverse(_mat_inv, _Uptri_->_Etrans_head, _COLUMN_);
    M_free(_Uptri_->_matrix);
    M_free(_Lowtri_->_matrix);
    free(_Uptri_);
    free(_Lowtri_);
    return _mat_inv;
}

int M_Swap(Matrix *_mat, int _line_1, int _line_2, int line_setting) {
    _line_1 = _line_1 - 1;
    _line_2 = _line_2 - 1;
    int i;
    MATRIX_TYPE temp;
    if (line_setting == _ROW_) {
        if ((_line_1 < _mat->row) && (_line_2 < _mat->row)) {
            for (i = 0; i < (_mat->column); i++) {
                temp = _mat->data[_line_1 * (_mat->column) + i];
                _mat->data[_line_1 * (_mat->column) + i] = _mat->data[_line_2 * (_mat->column) + i];
                _mat->data[_line_2 * (_mat->column) + i] = temp;
            }
        } else {
            printf(M_swap_004);
            system("pause");
        }
    } else {
        if ((_line_1 < _mat->column) && (_line_2 < _mat->column)) {
            for (i = 0; i < (_mat->row); i++) {
                temp = _mat->data[_line_1 + (_mat->column) * i];
                _mat->data[_line_1 + (_mat->column) * i] = _mat->data[_line_2 + (_mat->column) * i];
                _mat->data[_line_2 + (_mat->column) * i] = temp;
            }
        } else {
            printf(M_swap_004);
            system("pause");
        }
    }
    return 0;
}

Matrix *M_Cut(Matrix *_mat, int row_head, int row_tail, int column_head, int column_tail) {
    Matrix *mat_result = NULL;
    if (row_tail < 0) {
        if (row_tail == _END_) {
            row_tail = _mat->row;
        } else {
            printf(M_Cut_007);
            system("pause");
        }
    }

    if (row_head < 0) {
        if (row_head == _END_) {
            row_head = _mat->row;
        } else {
            printf(M_Cut_007);
            system("pause");
        }
    }

    if (column_tail < 0) {
        if (column_tail == _END_) {
            column_tail = _mat->column;
        } else {
            printf(M_Cut_007);
            system("pause");
        }
    }

    if (column_head < 0) {
        if (column_head == _END_) {
            column_head = _mat->column;
        } else {
            printf(M_Cut_007);
            system("pause");
        }
    }

    if ((row_tail > _mat->row) || (column_tail > _mat->column)) {
        printf(M_Cut_005);
        system("pause");
    } else {
        if ((row_head > row_tail) || (column_head > column_tail)) {
            printf(M_Cut_006);
            system("pause");
        } else {
            row_head = row_head - 1;
            column_head = column_head - 1;
            mat_result = (Matrix *) malloc(sizeof(Matrix));
            mat_result->row = row_tail - row_head;
            mat_result->column = column_tail - column_head;
            mat_result->data = (MATRIX_TYPE *) malloc(sizeof(MATRIX_TYPE) * (mat_result->row) * (mat_result->column));
            int i, j;
            for (i = 0; i < (row_tail - row_head); i++) {
                for (j = 0; j < (column_tail - column_head); j++) {
                    mat_result->data[i * (mat_result->column) + j] = _mat->data[(i + row_head) * (_mat->column) +
                                                                                (j + column_head)];
                }
            }
        }
    }
    return mat_result;
}

Matrix *M_T(Matrix *_mat_source) {
    Matrix *_mat = (Matrix *) malloc(sizeof(Matrix));
    _mat->column = _mat_source->row;
    _mat->row = _mat_source->column;
    MATRIX_TYPE *data = (MATRIX_TYPE *) malloc(sizeof(MATRIX_TYPE) * (_mat->column) * (_mat->row));
    _mat->data = data;
    int i, j;
    for (i = 0; i < (_mat->row); i++) {
        for (j = 0; j < _mat->column; j++) {
            data[i * (_mat->column) + j] = _mat_source->data[j * (_mat_source->column) + i];
        }
    }
    return _mat;
}

int M_free(Matrix *_mat) {
    free(_mat->data);
    (_DETAILED_>=3)?printf(">>Matrix_%x has been freed.\n", _mat):0;
    free(_mat);
    return 0;
}



MATRIX_TYPE M_norm(Matrix *_mat, int Setting) {
    MATRIX_TYPE *data = _mat->data;
    int row = _mat->row;
    int column = _mat->column;
    MATRIX_TYPE Val_norm = 0;
    int i, j;
    if (row == _ONE_ || column == _ONE_) {
        switch (Setting) {
            case 1: {
                for (i = 0; i < row; i++) {
                    for (j = 0; j < column; j++) {
                        Val_norm += fabs(data[i * (column) + j]);
                    }
                }
                break;
            }
            case 2: {
                for (i = 0; i < row; i++) {
                    for (j = 0; j < column; j++) {
                        Val_norm += data[i * (column) + j] * data[i * (column) + j];
                    }
                }
                Val_norm = pow(Val_norm, 0.5);
                break;
            }
            case INF: {
                Matrix *M_temp_0, *M_temp_1;
                M_temp_0 = M_abs(_mat);
                M_temp_1 = M_max(M_temp_0);
                int temp_num = M_temp_1->data[0];
                Val_norm = (M_temp_0)->data[temp_num];
                M_free(M_temp_0);
                M_free(M_temp_1);
                break;
            }
            default: {
                for (i = 0; i < row; i++) {
                    for (j = 0; j < column; j++) {
                        Val_norm += pow(data[i * (column) + j], Setting);
                    }
                }
                if (Val_norm < 0) {
                    printf(M_norm_warm_01);
                }
                Val_norm = pow(Val_norm, 1.0 / Setting);
                break;
            }
        }
    } else {
        switch (Setting) {
            case 1: {
                Matrix *M_temp_0, *M_temp_1, *M_temp_2;
                M_temp_0 = M_abs(_mat);
                M_temp_1 = M_sum(M_temp_0);
                M_temp_2 = M_max(M_temp_1);
                int temp_num = M_temp_2->data[0];
                Val_norm = (M_temp_1)->data[temp_num];
                M_free(M_temp_0);
                M_free(M_temp_1);
                M_free(M_temp_2);
                break;
            }
            case 2: {
                Matrix *M_temp_0, *M_temp_1;
                M_temp_0 = M_T(_mat);
                M_temp_1 = M_mul(M_temp_0, _mat);
                M_eigen_struct *M_temp_1_eigen = M_eigen_max(M_temp_1);
                Val_norm = M_temp_1_eigen->eigen_value;
                M_free(M_temp_0);
                M_free(M_temp_1);
                M_free(M_temp_1_eigen->eigen_matrix);
                free(M_temp_1_eigen);
                break;
            }
            case INF: {
                Matrix *M_temp_0, *M_temp_1, *M_temp_2, *M_temp_;
                M_temp_ = M_T(_mat);
                M_print(M_temp_);
                M_temp_0 = M_abs(M_temp_);
                M_print(M_temp_0);
                M_temp_1 = M_sum(M_temp_0);
                M_print(M_temp_1);
                M_temp_2 = M_max(M_temp_1);
                M_print(M_temp_2);
                int temp_num = M_temp_2->data[0];
                Val_norm = (M_temp_1)->data[temp_num];
                M_free(M_temp_);
                M_free(M_temp_0);
                M_free(M_temp_1);
                M_free(M_temp_2);
                break;
            }
            case FRO: {
                for (i = 0; i < row; i++) {
                    for (j = 0; j < column; j++) {
                        Val_norm += data[i * (column) + j] * data[i * (column) + j];
                    }
                }
                Val_norm = pow(Val_norm, 0.5);
                break;
            }
            default: {
                printf(M_norm_022);
                system("pause");
                break;
            }
        }
    }
    return Val_norm;
}

Matrix *M_abs(Matrix *_mat_origin) {
    Matrix *_mat = (Matrix *) malloc(sizeof(Matrix));
    _mat->row = _mat_origin->row;
    _mat->column = _mat_origin->column;
    int size = _mat->row * _mat->column;
    _mat->data = (MATRIX_TYPE *) malloc((size) * sizeof(MATRIX_TYPE));
    int i;
    for (i = 0; i < size; i++) {
        _mat->data[i] = fabs(_mat_origin->data[i]);
    }

    return _mat;
}

Matrix *M_numul(Matrix *_mat, MATRIX_TYPE _num) {
    MATRIX_TYPE *data = _mat->data;
    int Size_mat = (_mat->row) * (_mat->column), i;
    for (i = 0; i < Size_mat; i++) {
        data[i] = data[i] * _num;
    }
    return _mat;
}


Matrix *M_Zeros(int row, int column) {
    Matrix *Zero_mat = (Matrix *) malloc(sizeof(Matrix));
    Zero_mat->column = column;
    Zero_mat->row = row;
    int size = row * column, i;
    MATRIX_TYPE *data = (MATRIX_TYPE *) malloc((size) * sizeof(MATRIX_TYPE));
    for (i = 0; i < size; i++) {
        data[i] = 0;
    }
    Zero_mat->data = data;
    return Zero_mat;
}

Matrix *M_Ones(int row, int column) {
    Matrix *Zero_mat = (Matrix *) malloc(sizeof(Matrix));
    Zero_mat->row = row;
    Zero_mat->column = column;
    int size = row * column, i;
    MATRIX_TYPE *data = (MATRIX_TYPE *) malloc((size) * sizeof(MATRIX_TYPE));
    for (i = 0; i < size; i++) {
        data[i] = 1;
    }
    Zero_mat->data = data;
    return Zero_mat;
}


Matrix *M_sum(Matrix *_mat) {
    Matrix *mat_result = (Matrix *) malloc(sizeof(Matrix));
    int row = _mat->row, column = _mat->column;
    int i, j, size = row * column;
    if (row == _ONE_ || column == _ONE_) {
        MATRIX_TYPE *data = (MATRIX_TYPE *) malloc(sizeof(MATRIX_TYPE));
        data[0] = 0;
        for (i = 0; i < (size); i++) {
            data[0] = data[0] + _mat->data[i];
        }
        mat_result->row = 1;
        mat_result->column = 1;
        mat_result->data = data;
    } else {
        MATRIX_TYPE *data = (MATRIX_TYPE *) malloc(sizeof(MATRIX_TYPE) * column);
        for (i = 0; i < (column); i++) {
            data[i] = 0;
            for (j = 0; j < (row); j++) {
                data[i] = data[i] + _mat->data[j * column + i];
            }
        }
        mat_result->row = 1;
        mat_result->column = column;
        mat_result->data = data;
    }
    return mat_result;
}

Matrix *M_min(Matrix *_mat) {
    Matrix *mat_result = (Matrix *) malloc(sizeof(Matrix));
    int row = _mat->row, column = _mat->column;
    int i, j, size = row * column;
    if (row == _ONE_ || column == _ONE_) {
        MATRIX_TYPE *data = (MATRIX_TYPE *) malloc(sizeof(MATRIX_TYPE));
        data[0] = Min_position(_mat->data, size);
        mat_result->row = 1;
        mat_result->column = 1;
        mat_result->data = data;
    } else {
        MATRIX_TYPE *data = (MATRIX_TYPE *) malloc(sizeof(MATRIX_TYPE) * column);
        MATRIX_TYPE *temp_data = (MATRIX_TYPE *) malloc(sizeof(MATRIX_TYPE) * row);
        for (i = 0; i < (column); i++) {
            for (j = 0; j < (row); j++) {
                temp_data[j] = _mat->data[j * column + i];
            }
            data[i] = Min_position(temp_data, row);
        }
        mat_result->row = 1;
        mat_result->column = column;
        mat_result->data = data;
    }
    return mat_result;
}

int Min_position(MATRIX_TYPE *data, int size) {
    MATRIX_TYPE Val_min = data[size - 1];
    int min_position = size - 1, i;
    for (i = size - 2; i >= 0; i--) {
        if (data[i] <= Val_min) {
            Val_min = data[i];
            min_position = i;
        }
    }
    return min_position;
}

Matrix *M_max(Matrix *_mat) {
    Matrix *_mat_ = Matrix_copy(_mat);
    _mat_ = M_numul(_mat_, -1);
    Matrix *mat_result = M_min(_mat_);
    M_free(_mat_);
    return mat_result;
}


M_eigen_struct *M_eigen_max(Matrix *_mat) { 
    M_eigen_struct *M_eigen_max = NULL;
    if (_mat->column == _mat->row) {
        Matrix *mat_z = M_Ones(_mat->column, 1), *mat_temp_1 = NULL, *mat_temp_2 = NULL;
        Matrix *mat_y = NULL, *mat_z_gap = NULL;
        MATRIX_TYPE m_value = 0, mat_z_gap_norm = 1;
        MATRIX_TYPE deta = 1e-7;
        int temp_num = 0;

        while (mat_z_gap_norm > deta) {
            mat_y = M_mul(_mat, mat_z);
            mat_temp_1 = M_max(mat_y);
            temp_num = ((mat_temp_1)->data[0]);
            m_value = mat_y->data[temp_num];
            mat_temp_2 = mat_z;
            mat_z = M_numul(mat_y, 1 / m_value);
            mat_z_gap = M_add_sub(1, mat_z, 1, mat_temp_2);
            mat_z_gap_norm = M_norm(mat_z_gap, 2);
            M_free(mat_temp_1);
            M_free(mat_temp_2);
            M_free(mat_z_gap);
        }

        M_eigen_max = (M_eigen_struct *) malloc(sizeof(M_eigen_struct));
        M_eigen_max->eigen_value = m_value;
        M_eigen_max->eigen_matrix = mat_z;
    } else {
        printf(M_eigen_max_021);
        system("pause");
    }
    return M_eigen_max;
}

Matrix ** M_eigen (Matrix *_mat) {
    Matrix ** M_array_eigen_vec = NULL;
    if (_mat->column == _mat->row) {
        M_array_eigen_vec = (Matrix **)malloc(sizeof(Matrix *)*2);
        enum{val=0, vec=1};
        Matrix *eigen_value = M_eigen_val(_mat);
        M_array_eigen_vec[val] = eigen_value;
        int eigen_count, dim = _mat->column, i, j, ik, jk;
        Matrix *eigen_vector = NULL, *_mat_ = NULL;
        eigen_vector = M_Zeros(dim,dim);
        M_array_eigen_vec[vec] = eigen_vector;
        double eigen_value_temp ;
        MATRIX_TYPE coe; 
        for(eigen_count=0;eigen_count<dim;eigen_count++){
            _mat_ = Matrix_copy(_mat);
            eigen_value_temp = eigen_value->data[eigen_count];
            for (i = 0; i < dim; i++){
                _mat_->data[i * _mat_->column + i] -= eigen_value_temp; 
            }
            for (i = 0; i < dim-1; i++){
                coe = _mat_->data[i * dim + i];
                for (j = i; j<dim; j++){
                    _mat_->data[i * dim + j] /= coe;
                }
                for (ik = i + 1; ik < dim; ik++){
                    coe = _mat_->data[ik * dim + i];
                    for (jk = i; jk < dim; jk++){
                        _mat_->data[ik * dim + jk] -= coe * _mat_->data[i * dim + jk];
                    }
                }
            }
            double sum1 = 1;
            eigen_vector->data[(dim - 1) * dim + eigen_count] = 1;
            for (ik = dim - 2; ik >= 0; ik--)
            {
                double sum2 = 0;
                for (jk = ik + 1; jk < dim; jk++)
                {
                    sum2 += _mat_->data[ik * dim + jk] * eigen_vector->data[jk * dim + eigen_count];
                }
                sum2 = -sum2 / _mat_->data[ik * dim + ik];
                sum1 += sum2 * sum2;
                eigen_vector->data[ik * dim + eigen_count] = sum2;
            }
            M_free(_mat_);
            sum1 = sqrt(sum1);
            for (int i = 0; i < dim; i++){
                eigen_vector->data[i * dim + eigen_count] /= sum1;
            }
        }
    }else{
        printf(M_eigen_026);
        system("pause");
    }
    return M_array_eigen_vec;
}

Matrix* householder(Matrix * _x) {
    Matrix *H = NULL;
    Matrix *y = M_Zeros(_x->row,_x->column);
    y->data[0] = M_norm(_x, 2);
    Matrix *w = NULL;
    if(_x->data[0] > 0){
        w = M_add_sub(1,_x,-1,y);
        M_numul(w,1/M_norm(w, 2));
    }else{
        w = M_add_sub(1,_x,1,y);
        M_numul(w,1/M_norm(w, 2));
    }
    Matrix *I= M_I(_x->row);
    Matrix *w_T = M_T(w);
    Matrix *M_dot = M_mul(w,w_T);
    H = M_add_sub(1,I,2,M_dot);
    M_free(y);
    M_free(w);
    M_free(I);
    M_free(w_T);
    M_free(M_dot);
    return H;
}


Matrix ** M_QR(Matrix * _mat){
    Matrix ** M_array_Q_R = (Matrix **)malloc(sizeof(Matrix *)*2);
    enum{q=0, r=1};
    M_array_Q_R[q] = NULL;
    M_array_Q_R[r] = NULL;
    int i, j, k, dim = _mat->row;
    Matrix *Q=NULL, *D=NULL, *Qi=NULL, *Hi=NULL, *x=NULL, *temp_1=NULL, *temp_2=NULL;
    Matrix * Ri = Matrix_copy(_mat); 
    for(i=0;i<dim;i++){
        x = M_Cut(_mat,i+1,_END_,i+1,i+1);
        Hi = householder(x);
        M_free(x);
        temp_1 = M_Cut(Ri,i+1,_END_,i+1,_END_);
        temp_2 = M_mul(Hi,temp_1);
        M_free(temp_1);
        for(j=0;j<dim-i;j++){
            for(k=0;k<dim-i;k++){
                Ri->data[(j+i)*dim+(k+i)] = temp_2->data[j*(dim-i)+k];
            }
        }
        M_free(temp_2);
        Qi = M_I(dim);
        for(j=0;j<dim-i;j++){ // Qi[i:, i:] = Hi
            for(k=0;k<dim-i;k++){
                Qi->data[(j+i)*dim+(k+i)] = Hi->data[j*(dim-i)+k];
            }
        }
        M_free(Hi);
        if (i == 0){
            Q = Matrix_copy(Qi);
        }else{
            temp_1 = Q;
            Q = M_mul(Qi,temp_1);
            M_free(temp_1);
        }
        M_free(Qi);
    }
    D = M_I(dim);
    for(i=0;i<dim;i++){
        D->data[i] = (Ri->data[i*dim+i] < 0)?-1:1;
    }
    M_array_Q_R[r] = M_mul(D,Ri);
    temp_1 = M_T(Q);
    temp_2 = M_Dia_Inv(D);
    M_array_Q_R[q] = M_mul(temp_1, temp_2);
    M_free(temp_1);
    M_free(temp_2);
    M_free(Ri);
    M_free(D);
    M_free(Q);
    return M_array_Q_R;
}

Matrix * M_eigen_val(Matrix * _mat){
    (_DETAILED_>=2)?printf(">>Eigen_Value(Matrix_%x)=\n", _mat):0;
    (_DETAILED_>=2)?printf("...CACULATING...\n#if need help: use \'help(\"M_eigen_val\")\'#\n"):0;
    double *eigen_val = NULL;
    Matrix ** M_array_Q_R = NULL; // ����Q/R�����ַ
    enum{q=0, r=1};
    double eps = 1e-5, delta = 1; // ���ü������
    int i, dim=_mat->row, epoch = 0;
    Matrix *Ak0, *Ak, *Qk, *Rk, *M_eigen_val;
    Ak = Matrix_copy(_mat);
    while((delta > eps)&&(epoch < _MAX_LOOP_NUM_)){
        M_array_Q_R = M_QR(Ak);
        Qk = M_array_Q_R[q];
        Rk = M_array_Q_R[r];
        Ak0 = Ak;
        Ak = M_mul(Rk, Qk);
        delta = 0;
        for(i=0;i<dim;i++){
            delta += fabs(Ak->data[i*dim+i]-Ak0->data[i*dim+i]);
        }
        M_free(Ak0);
        M_free(Qk);
        M_free(Rk);
        free(M_array_Q_R);
        (_progress_bar_)?progress_bar(epoch,_MAX_LOOP_NUM_):0;
        epoch++;
    }
    if(epoch >= _MAX_LOOP_NUM_){
        printf("\n>>ATTENTION: QR Decomposition end with delta = %.3e!(epoch=%d, eps=%.2e)\n", delta,_MAX_LOOP_NUM_,eps);
    }
    M_eigen_val = (Matrix*)malloc(sizeof(Matrix));
    M_eigen_val->column = dim;
    M_eigen_val->row = 1;
    eigen_val = (double*)malloc(sizeof(double)*dim);
    for(i=0;i<dim;i++){
        eigen_val[i] = Ak->data[i*dim+i];
    }
    M_eigen_val->data = eigen_val;
    M_free(Ak);
    (_DETAILED_>=2)?printf("...END...\n>>Eigen_Value = (Matrix_%x)\n", M_eigen_val):0;
    return M_eigen_val;
}

void progress_bar(int count, int total) {
    double num = (int)((1.0*count/total)*50);
    printf("%% %.2f[", num*2);
    for(int i = 0; i < 50; i++){
        (i < num)?printf(">"):printf(" ");
    }
    printf("]\r");
}

void update_feature_map(afl_state_t *afl){
  u32 *ptr = (u32 *)afl->virgin_bits;
  u32  i = ((afl->fsrv.real_map_size + 3) >> 2);
  u32  ret = 0;
  u32 id = 0;
  memset(afl->feature_map, 0, afl->fsrv.map_size * sizeof(u32));
  afl->num_edge = 1;

  while (i--) {
    u32 v = *(ptr++);

    if (likely(v == 0xffffffffU)) {
      id +=4;
      continue; 
    }
    if ((v & 0x000000ffU) != 0x000000ffU) {
      afl->feature_map[id + 0] = afl->num_edge;
      afl->num_edge++;
    }
    if ((v & 0x0000ff00U) != 0x0000ff00U) {
      afl->feature_map[id + 1] = afl->num_edge;
      afl->num_edge++;
    }
    if ((v & 0x00ff0000U) != 0x00ff0000U) {
      afl->feature_map[id + 2] = afl->num_edge;
      afl->num_edge++;
    }
    if ((v & 0xff000000U) != 0xff000000U) {
      afl->feature_map[id + 3] = afl->num_edge;
      afl->num_edge++;
    }

    id +=4;
  }


}

float distance(float *a, float *b, int dim)
{
	int i;
	float sum=0,res=0;
	for(i=0;i<dim;i++)
	{
		sum=sum+((a[i]-b[i])*(a[i]-b[i]));
	}
	res=sqrt(sum);
	return res;
}

/*
 * =====================================================================================
 *         Author:  BlackLight (http://0x00.ath.cx), <blacklight@autistici.org>
 *        Licence:  GNU GPL v.3
 *        Company:  DO WHAT YOU WANT CAUSE A PIRATE IS FREE, YOU ARE A PIRATE!
 *
 * =====================================================================================
 */
float ** km_new(float **data, int k, int row, int dim){
	int max_iteration=100;
	FILE *fa=fopen("centroids.out","w");

	float **cluster_centroid;
	float **cluster_distance;
	float **tmp;
	float *dist_sum;
	int *cluster_element_count;
	cluster_element_count=(int *)malloc(k*sizeof(int));
	int i,div,j,current_distance,current_cluster;
	
	int iteration=0;

	// memory for  cluster centroids	
	cluster_centroid=(float **)malloc(k*sizeof(float **));
	for(i=0;i<k;i++)
	{
		cluster_centroid[i]=(float *)malloc(dim*sizeof(float ));
	}

	cluster_distance=(float **)malloc(row*sizeof(float *));
	for(i=0;i<row;i++)
	{
		cluster_distance[i]=(float *)malloc(k*sizeof(float ));
	}

	// array to store cumulative sum of the distance from data to each centroid
	dist_sum=(float *)malloc(k*sizeof(float));

	//initialize a temporal array
	tmp=(float **)malloc(k*sizeof(float *));
	for(i=0;i<k;i++)
	{
		tmp[i]=(float *)malloc(dim*sizeof(float));
	}

	//kmeans iterations
	while(iteration<max_iteration)
	{

		if(iteration==0)
		{
			//initialize centroids. if first iteration, get centroids from the original data array in a uniform distribution
			div=(row-k)/k;
			for(i=0;i<k;i++)
			{
				for(j=0;j<dim;j++)
				{
					cluster_centroid[i][j]=data[i*div][j];
				}
			}
		}// first iteration
			
		//find distance between each datapoint and each cluster
		for(i=0;i<row;i++)
		{
			for(j=0;j<k;j++)
			{
				cluster_distance[i][j]=distance(data[i],cluster_centroid[j],dim);
			}
		}

		//initialize to zero
		for(i=0;i<k;i++)
		{
			cluster_element_count[i]=0;
			for(j=0;j<dim;j++)
			{
				tmp[i][j]=0;
			}
		}

		// clear the error array
		for(i=0;i<k;i++)
		{
			dist_sum[i]=0;
		}

		//find to which cluster centroids, each data point is nearest to
		for(i=0;i<row;i++)
		{
			current_distance=10000000;
			current_cluster=-1;
			for(j=0;j<k;j++)
			{
				if(cluster_distance[i][j]<current_distance)
				{
					current_cluster=j;
					current_distance=cluster_distance[i][j];
				}
			}
			dist_sum[current_cluster]=dist_sum[current_cluster]+current_distance;
			cluster_element_count[current_cluster]=cluster_element_count[current_cluster]+1;
			for(j=0;j<dim;j++)
			{
				tmp[current_cluster][j]=tmp[current_cluster][j]+data[i][j];
			}
		}

		// update centroids
		for(i=0;i<k;i++)
		{
			if(cluster_element_count[i]==0)                                             // no points in that cluster
			{
				continue;
			}
			for(j=0;j<dim;j++)
			{
				cluster_centroid[i][j]=tmp[i][j]/(float)cluster_element_count[i];
			}
			// printf("\nIteration %d ", iteration);
			dist_sum[i]=dist_sum[i]/(float)cluster_element_count[i];  	
		}
		iteration=iteration+1;
	}// iterations

	//All the iterations are over. Now write the centroids to the file
	for(i=0;i<k;i++)
	{
		for(j=0;j<dim;j++)
		{
			fprintf(fa,"%f ",cluster_centroid[i][j]);
		}
		fprintf(fa,"\n");
	}

	//free the arrays
	free(dist_sum);
	free(cluster_element_count);
	free(tmp);
	free(cluster_distance);
	fclose(fa);

	return cluster_centroid;
}


static void
__kmeans_init_centers ( kmeans_t *km )
{
	int i, j, k, l,
	    index_found = 0,
	    max_index = 0,
	    assigned_centers = 0,
	    *assigned_centers_indexes = NULL;

	float dist = 0.0,
		  max_dist = 0.0;

	for ( i=0; i < km->dataset_size; i++ )
	{
		dist = 0.0;

		for ( j=0; j < km->dataset_dim; j++ )
		{
			dist += ( km->dataset[i][j] ) * ( km->dataset[i][j] );
		}

		if ( dist > max_dist )
		{
			max_dist = dist;
			max_index = i;
		}
	}

	for ( i=0; i < km->dataset_dim; i++ )
	{
		km->centers[0][i] = km->dataset[max_index][i];
	}

	if ( !( assigned_centers_indexes = (int*) realloc ( assigned_centers_indexes, (++assigned_centers) * sizeof ( int ))))
	{
		return;
	}

	assigned_centers_indexes[ assigned_centers - 1 ] = max_index;

	for ( i=1; i < km->k; i++ )
	{
		max_dist = 0.0;
		max_index = 0;

		for ( j=0; j < km->dataset_size; j++ )
		{
			index_found = 0;
			
			for ( k=0; k < assigned_centers && !index_found; k++ )
			{
				if ( assigned_centers_indexes[k] == j )
				{
					index_found = 1;
				}
			}

			if ( index_found )
				continue;

			dist = 0.0;

			for ( k=0; k < assigned_centers; k++ )
			{
				for ( l=0; l < km->dataset_dim; l++ )
				{
					dist += ( km->dataset[j][l] - km->centers[k][l] ) * ( km->dataset[j][l] - km->centers[k][l] );
				}
			}

			if ( dist > max_dist )
			{
				max_dist = dist;
				max_index = j;
			}
		}

		for ( j=0; j < km->dataset_dim; j++ )
		{
			km->centers[i][j] = km->dataset[max_index][j];
		}

		if ( !( assigned_centers_indexes = (int*) realloc ( assigned_centers_indexes, (++assigned_centers) * sizeof ( int ))))
		{
			return;
		}

		assigned_centers_indexes[ assigned_centers - 1 ] = max_index;
	}

	free ( assigned_centers_indexes );
}		/* -----  end of function kmeans_init_centers  ----- */


kmeans_t*
kmeans_new ( float **dataset, const int dataset_size, const int dataset_dim, const int K )
{
	int i, j;
	kmeans_t *km = NULL;

	if ( !( km = (kmeans_t*) malloc ( sizeof ( kmeans_t ))))
	{
		return NULL;
	}

	if ( !( km->dataset = (float**) calloc ( dataset_size, sizeof ( float* ))))
	{
		return NULL;
	}

	for ( i=0; i < dataset_size; i++ )
	{
		if ( !( km->dataset[i] = (float*) calloc ( dataset_dim, sizeof ( float ))))
		{
			return NULL;
		}

		for ( j=0; j < dataset_dim; j++ )
		{
			km->dataset[i][j] = dataset[i][j];
		}
	}

	km->dataset_size = dataset_size;
	km->dataset_dim = dataset_dim;
	km->k = K;

	if ( !( km->clusters = (float***) calloc ( K, sizeof ( float** ))))
	{
		return NULL;
	}

	if ( !( km->cluster_sizes = (int*) calloc ( K, sizeof ( int* ))))
	{
		return NULL;
	}

	if ( !( km->centers = (float**) calloc ( K, sizeof ( float* ))))
	{
		return NULL;
	}

	for ( i=0; i < K; i++ )
	{
		if ( !( km->centers[i] = (float*) calloc ( dataset_dim, sizeof ( float ))))
		{
			return NULL;
		}
	}

	__kmeans_init_centers ( km );
	return km;
}		/* -----  end of function kmeans_new  ----- */


static int
__kmeans_step ( kmeans_t *km )
{
	int i, j, k,
	    best_center = 0;

	float dist = 0.0,
		  min_dist = DBL_MAX,
		  **old_centers = NULL;

	if ( km->clusters[0] )
	{
		for ( i=0; i < km->k; i++ )
		{
			for ( j=0; j < km->cluster_sizes[i]; j++ )
			{
				free ( km->clusters[i][j] );
				km->clusters[i][j] = NULL;
			}

			free ( km->clusters[i] );
			km->clusters[i] = NULL;
			km->cluster_sizes[i] = 0;
		}
	}

	if ( !( old_centers = (float**) alloca ( km->k * sizeof ( float* ))))
	{
		return -1;
	}

	for ( i=0; i < km->k; i++ )
	{
		if ( !( old_centers[i] = (float*) alloca ( km->dataset_dim * sizeof ( float ))))
		{
			return -1;
		}

		for ( j=0; j < km->dataset_dim; j++ )
		{
			old_centers[i][j] = km->centers[i][j];
		}
	}

	for ( i=0; i < km->dataset_size; i++ )
	{
		min_dist = DBL_MAX;
		best_center = 0;

		for ( j=0; j < km->k; j++ )
		{
			dist = 0.0;

			for ( k=0; k < km->dataset_dim; k++ )
			{
				dist += ( km->dataset[i][k] - km->centers[j][k] ) * ( km->dataset[i][k] - km->centers[j][k] );
			}

			if ( dist < min_dist )
			{
				min_dist = dist;
				best_center = j;
			}
		}

		if ( !( km->clusters[best_center] = (float**) realloc ( km->clusters[best_center], (++(km->cluster_sizes[best_center])) * sizeof ( float* ))))
		{
			return -1;
		}

		if ( !( km->clusters [best_center] [km->cluster_sizes[best_center]-1] = (float*) calloc ( km->dataset_dim, sizeof ( float ))))
		{
			return -1;
		}

		for ( j=0; j < km->dataset_dim; j++ )
		{
			km->clusters [best_center] [km->cluster_sizes[best_center]-1] [j] = km->dataset[i][j];
		}
	}

	for ( i=0; i < km->k; i++ )
	{
		for ( j=0; j < km->dataset_dim; j++ )
		{
			km->centers[i][j] = 0.0;

			for ( k=0; k < km->cluster_sizes[i]; k++ )
			{
				km->centers[i][j] += km->clusters[i][k][j];
			}

			if ( km->cluster_sizes[i] != 0 )
			{
				km->centers[i][j] /= (float) km->cluster_sizes[i];
			}
		}
	}

	for ( i=0; i < km->k; i++ )
	{
		for ( j=0; j < km->dataset_dim; j++ )
		{
			if ( km->centers[i][j] != old_centers[i][j] )
			{
				return 1;
			}
		}
	}

	return 0;
}		/* -----  end of function __kmeans_step  ----- */



void
kmeans ( kmeans_t *km )
{
	while ( __kmeans_step ( km ) != 0 );
}		/* -----  end of function kmeans  ----- */



static float
__kmeans_heuristic_coefficient ( kmeans_t *km )
{
	int i, j, k;
	float distorsion = 0.0;

	for ( i=0; i < km->k; i++ )
	{
		for ( j=0; j < km->cluster_sizes[i]; j++ )
		{
			for ( k=0; k < km->dataset_dim; k++ )
			{
				distorsion += ( km->centers[i][k] - km->clusters[i][j][k] ) * ( km->centers[i][k] - km->clusters[i][j][k] );
			}
		}
	}

	return distorsion + km->k * log ( km->dataset_size );
}		/* -----  end of function __kmeans_heuristic_coefficient  ----- */


void
kmeans_free ( kmeans_t *km )
{
	int i, j;

	for ( i=0; i < km->k; i++ )
	{
		for ( j=0; j < km->cluster_sizes[i]; j++ )
		{
			free ( km->clusters[i][j] );
			km->clusters[i][j] = NULL;
		}

		free ( km->clusters[i] );
		km->clusters[i] = NULL;
	}

	free ( km->clusters );
	km->clusters = NULL;

	free ( km->cluster_sizes );
	km->cluster_sizes = NULL;

	for ( i=0; i < km->k; i++ )
	{
		free ( km->centers[i] );
		km->centers[i] = NULL;
	}

	free ( km->centers );
	km->centers = NULL;

	for ( i=0; i < km->dataset_size; i++ )
	{
		free ( km->dataset[i] );
		km->dataset[i] = NULL;
	}

	free ( km->dataset );
	km->dataset = NULL;

	free ( km );
	km = NULL;
}		/* -----  end of function kmeans_free  ----- */


kmeans_t*
kmeans_auto ( float **dataset, int dataset_size, int dataset_dim )
{
	int i;

	float heuristic = 0.0,
		  best_heuristic = DBL_MAX;

	kmeans_t *km = NULL,
		    *best_km = NULL;

	for ( i=1; i <= dataset_size; i++ )
	{
		if ( !( km = kmeans_new ( dataset, dataset_size, dataset_dim, i )))
			return NULL;

		kmeans ( km );
		heuristic = __kmeans_heuristic_coefficient ( km );

		if ( heuristic < best_heuristic )
		{
			if ( best_km )
			{
				kmeans_free ( best_km );
			}

			best_km = km;
			best_heuristic = heuristic;
		} else {
			kmeans_free ( km );
		}
	}
	
	return best_km;
}		/* -----  end of function kmeans_auto  ----- */

int kmeans_main(afl_state_t *afl){
  update_feature_map(afl);

  u64 start_time = ((afl->prev_run_time + get_cur_time() - afl->start_time) / 1000);

  int observations_size = afl->queued_items;
  int vector_size = afl->num_edge;
  int k = afl->centers_num;
  float **observations;
  
  observations = (float **) malloc(sizeof(float *) * observations_size);
  for (int i = 0; i < observations_size; i++){
    observations[i] = (float *) malloc(sizeof(float) * vector_size);
    memset(observations[i], 0, sizeof(float) * vector_size);
  }

  u32 map_size = afl->fsrv.map_size;
  int epoch = afl->queued_items/observations_size;
  float ** centers;
  for(int cur_epoch = 0; cur_epoch < epoch; cur_epoch++){
    for (int i = 0; i < observations_size; i++){
      memset(observations[i], 0, sizeof(float) * vector_size);
    }

    for (u32 i = 0; i < observations_size; i++) {
      u32 tid;
      tid = rand_below(afl, afl->queued_items);
      if (likely(!afl->queue_buf[tid]->disabled)) {
        u8* out_buf = queue_testcase_get(afl, afl->queue_buf[tid]);
        u32 len = afl->queue_buf[tid]->len;
        common_fuzz_stuff(afl, out_buf, len);

        u32 j = 0;
        u8 *src = afl->fsrv.trace_bits;
        while (j < map_size) {
          u8 v = *src;
          if(v){
            u32 idx = afl->feature_map[j];
            observations[i][idx] = (float)v;
          }
          src++;
          ++j;
        }
      }
    }

    centers = km_new(observations, k, observations_size, vector_size);

  }

  
  u64 end_time = ((afl->prev_run_time + get_cur_time() - afl->start_time) / 1000);
  for(int i = 0;i < k;i++){
    if(afl->centers[i]) free(afl->centers[i]);

    float* tmp = (float *)malloc(sizeof(float) * map_size);
    memset(tmp, 0, sizeof(float) * map_size);
    for(int j = 0;j < map_size;j++){
      u32 idx = afl->feature_map[j];
      if(centers[i][idx] != 0){
        tmp[j] = centers[i][idx];
      } 
    }
    afl->centers[i] = tmp;
  }
  
  for (int i=0 ; i<observations_size ; ++i)
    free(observations[i]);
  free(observations);

  end_time = ((afl->prev_run_time + get_cur_time() - afl->start_time) / 1000);

	return 0;
}

float cal_distance(float* a, float* b, u32 map_size){
  //method two
  float sum = 0;
  float sum2 = 0;
  u32 j = 0;
  while (j < map_size) {
    float a_v = *a;
    float b_v = *b;

    if(a_v && b_v){
      sum++;
    }
    if(a_v || b_v){
      sum2++;
    }
      
    a++;
    b++;
    ++j;
  }
  return sum/sum2;
}


/* Take the current entry from the queue, fuzz it for a while. This
   function is a tad too long... returns 0 if fuzzed successfully, 1 if
   skipped or bailed out. */

u8 fuzz_one_original(afl_state_t *afl) {

  u32 len, temp_len;
  u32 j;
  u32 i;
  u8 *in_buf, *out_buf, *orig_in, *ex_tmp, *eff_map = 0;
  u64 havoc_queued = 0, orig_hit_cnt, new_hit_cnt = 0, prev_cksum;
  u32 splice_cycle = 0, perf_score = 100, orig_perf, eff_cnt = 1;

  u8 ret_val = 1, doing_det = 0;

  u8  a_collect[MAX_AUTO_EXTRA];
  u32 a_len = 0;

#ifdef IGNORE_FINDS

  /* In IGNORE_FINDS mode, skip any entries that weren't in the
     initial data set. */

  if (afl->queue_cur->depth > 1) return 1;

#else

  if (unlikely(afl->custom_mutators_count)) {

    /* The custom mutator will decide to skip this test case or not. */

    LIST_FOREACH(&afl->custom_mutator_list, struct custom_mutator, {

      if (el->afl_custom_queue_get &&
          !el->afl_custom_queue_get(el->data, afl->queue_cur->fname)) {

        return 1;

      }

    });

  }

  if (likely(afl->pending_favored)) {

    /* If we have any favored, non-fuzzed new arrivals in the queue,
       possibly skip to them at the expense of already-fuzzed or non-favored
       cases. */

    if ((afl->queue_cur->fuzz_level || !afl->queue_cur->favored) &&
        likely(rand_below(afl, 100) < SKIP_TO_NEW_PROB)) {

      return 1;

    }

  } else if (!afl->non_instrumented_mode && !afl->queue_cur->favored &&

             afl->queued_items > 10) {

    /* Otherwise, still possibly skip non-favored cases, albeit less often.
       The odds of skipping stuff are higher for already-fuzzed inputs and
       lower for never-fuzzed entries. */

    if (afl->queue_cycle > 1 && !afl->queue_cur->fuzz_level) {

      if (likely(rand_below(afl, 100) < SKIP_NFAV_NEW_PROB)) { return 1; }

    } else {

      if (likely(rand_below(afl, 100) < SKIP_NFAV_OLD_PROB)) { return 1; }

    }

  }

#endif                                                     /* ^IGNORE_FINDS */

  if (unlikely(afl->not_on_tty)) {

    ACTF(
        "Fuzzing test case #%u (%u total, %llu crashes saved, "
        "perf_score=%0.0f, exec_us=%llu, hits=%u, map=%u, ascii=%u)...",
        afl->current_entry, afl->queued_items, afl->saved_crashes,
        afl->queue_cur->perf_score, afl->queue_cur->exec_us,
        likely(afl->n_fuzz) ? afl->n_fuzz[afl->queue_cur->n_fuzz_entry] : 0,
        afl->queue_cur->bitmap_size, afl->queue_cur->is_ascii);
    fflush(stdout);

  }

  orig_in = in_buf = queue_testcase_get(afl, afl->queue_cur);
  len = afl->queue_cur->len;

  out_buf = afl_realloc(AFL_BUF_PARAM(out), len);
  if (unlikely(!out_buf)) { PFATAL("alloc"); }

  afl->subseq_tmouts = 0;

  afl->cur_depth = afl->queue_cur->depth;

  /*******************************************
   * CALIBRATION (only if failed earlier on) *
   *******************************************/

  if (unlikely(afl->queue_cur->cal_failed)) {

    u8 res = FSRV_RUN_TMOUT;

    if (afl->queue_cur->cal_failed < CAL_CHANCES) {

      afl->queue_cur->exec_cksum = 0;

      res =
          calibrate_case(afl, afl->queue_cur, in_buf, afl->queue_cycle - 1, 0);

      if (unlikely(res == FSRV_RUN_ERROR)) {

        FATAL("Unable to execute target application");

      }

    }

    if (unlikely(afl->stop_soon) || res != afl->crash_mode) {

      ++afl->cur_skipped_items;
      goto abandon_entry;

    }

  }

  /************
   * TRIMMING *
   ************/
  
  if (unlikely(!afl->non_instrumented_mode && !afl->queue_cur->trim_done &&
               !afl->disable_trim)) {

    u32 old_len = afl->queue_cur->len;

    u8 res = trim_case(afl, afl->queue_cur, in_buf);
    orig_in = in_buf = queue_testcase_get(afl, afl->queue_cur);

    if (unlikely(res == FSRV_RUN_ERROR)) {

      FATAL("Unable to execute target application");

    }

    if (unlikely(afl->stop_soon)) {

      ++afl->cur_skipped_items;
      goto abandon_entry;

    }

    /* Don't retry trimming, even if it failed. */

    afl->queue_cur->trim_done = 1;

    len = afl->queue_cur->len;

    /* maybe current entry is not ready for splicing anymore */
    if (unlikely(len <= 4 && old_len > 4)) --afl->ready_for_splicing_count;

  }

  memcpy(out_buf, in_buf, len);

  u64 fuzz_time = ((afl->prev_run_time + get_cur_time() - afl->start_time) / 1000);  
  if(afl->queued_items > afl->centers_num && (afl->queued_items >= 2 * afl->last_centers_realted_seeds)){
    kmeans_main(afl);

    afl->last_centers_realted_seeds = afl->queued_items;
    afl->centers_gen_time = fuzz_time;

    for (u32 c = 0; c < afl->queued_items; c++) {
      struct queue_entry * cur_node = afl->queue_buf[c];
      if(cur_node->initial_seed && cur_node->mutated_pos_num != -1){
        for(u32 i = 0;i < cur_node->len;i++){
          if(cur_node->mutated_pos[i].flag >= 1){
            M_free(cur_node->mutated_pos[i].A);
            M_free(cur_node->mutated_pos[i].b);

            cur_node->mutated_pos[i].A = M_I(afl->centers_num);
            cur_node->mutated_pos[i].b = M_Zeros(afl->centers_num,1);
          }
        }
      }
    }
  }

  if(afl->centers_gen_time > afl->queue_cur->vec_update_time){
    u32 map_size = afl->fsrv.map_size;
    float* cur = (float *)malloc(sizeof(float) * map_size);
    memset(cur, 0 ,sizeof(float) * map_size);

    common_fuzz_stuff(afl, out_buf, len);
    u32 j = 0;
    u8 *src = afl->fsrv.trace_bits;
    while (j < map_size) {
      u8 v = *src;
      if(v){
        cur[j] = (float)v;
      }
      src++;
      ++j;
    }

    for(u32 i = 0;i < afl->centers_num;i++){
      double distance = (double)cal_distance(cur, afl->centers[i], map_size);
      afl->queue_cur->feature_vec->data[i] = distance;
    }

    afl->queue_cur->vec_update_time = afl->centers_gen_time;
    
  }
  

  if(afl->queue_cur->len > afl->max_len){
    if(afl->history_mutation_sequence){
      free(afl->history_mutation_sequence);
      free(afl->new_mutation_sequence);
    }

    afl->history_mutation_sequence = (u32 *)calloc(afl->queue_cur->len, sizeof(u32));
    afl->new_mutation_sequence = (u32 *)calloc(afl->queue_cur->len, sizeof(u32));

    if(afl->max_len != 0){
      free(afl->dataset_reward);
      free(afl->hit_nums);
      free(afl->tmp_mutated_pos);
      free(afl->tmp_mutated_pos_flag);
    }
    

    afl->dataset_reward = (double *)calloc(afl->queue_cur->len, sizeof(double));
    afl->hit_nums = (double *)calloc(afl->queue_cur->len, sizeof(double));
    afl->tmp_mutated_pos = (u32 *)calloc(afl->queue_cur->len, sizeof(u32));
    afl->tmp_mutated_pos_flag = (u8 *)calloc(afl->queue_cur->len, sizeof(u8));

    afl->max_len = afl->queue_cur->len;
  }else{
    memset(afl->dataset_reward, 0, afl->max_len * sizeof(double));
    memset(afl->hit_nums, 0, afl->max_len * sizeof(double));
    memset(afl->tmp_mutated_pos_flag, 0, afl->max_len * sizeof(u8));
  }
  afl->history_mutation_sequence_idx = 0;
  afl->new_mutation_sequence_idx = 0;
  afl->tmp_mutated_pos_idx = 0;
  afl->from_splicing = 0;


  /*********************
   * PERFORMANCE SCORE *
   *********************/

  if (likely(!afl->old_seed_selection))
    orig_perf = perf_score = afl->queue_cur->perf_score;
  else
    afl->queue_cur->perf_score = orig_perf = perf_score =
        calculate_score(afl, afl->queue_cur);

  if (unlikely(perf_score <= 0 && afl->active_items > 1)) {

    goto abandon_entry;

  }

  if (unlikely(afl->shm.cmplog_mode &&
               afl->queue_cur->colorized < afl->cmplog_lvl &&
               (u32)len <= afl->cmplog_max_filesize)) {

    if (unlikely(len < 4)) {

      afl->queue_cur->colorized = CMPLOG_LVL_MAX;

    } else {

      if (afl->cmplog_lvl == 3 ||
          (afl->cmplog_lvl == 2 && afl->queue_cur->tc_ref) ||
          afl->queue_cur->favored ||
          !(afl->fsrv.total_execs % afl->queued_items) ||
          get_cur_time() - afl->last_find_time > 300000) {  // 300 seconds

        if (input_to_state_stage(afl, in_buf, out_buf, len)) {

          goto abandon_entry;

        }

      }

    }

  }

  /* Skip right away if -d is given, if it has not been chosen sufficiently
     often to warrant the expensive deterministic stage (fuzz_level), or
     if it has gone through deterministic testing in earlier, resumed runs
     (passed_det). */

  if (likely(afl->queue_cur->passed_det) || likely(afl->skip_deterministic) ||
      likely(perf_score <
             (afl->queue_cur->depth * 30 <= afl->havoc_max_mult * 100
                  ? afl->queue_cur->depth * 30
                  : afl->havoc_max_mult * 100))) {

    goto custom_mutator_stage;

  }

  /* Skip deterministic fuzzing if exec path checksum puts this out of scope
     for this main instance. */

  if (unlikely(afl->main_node_max &&
               (afl->queue_cur->exec_cksum % afl->main_node_max) !=
                   afl->main_node_id - 1)) {

    goto custom_mutator_stage;

  }

  doing_det = 1;

  /*********************************************
   * SIMPLE BITFLIP (+dictionary construction) *
   *********************************************/

#define FLIP_BIT(_ar, _b)                   \
  do {                                      \
                                            \
    u8 *_arf = (u8 *)(_ar);                 \
    u32 _bf = (_b);                         \
    _arf[(_bf) >> 3] ^= (128 >> ((_bf)&7)); \
                                            \
  } while (0)

  /* Single walking bit. */

  afl->stage_short = "flip1";
  afl->stage_max = len << 3;
  afl->stage_name = "bitflip 1/1";

  afl->stage_val_type = STAGE_VAL_NONE;

  orig_hit_cnt = afl->queued_items + afl->saved_crashes;

  prev_cksum = afl->queue_cur->exec_cksum;

  for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max; ++afl->stage_cur) {

    afl->stage_cur_byte = afl->stage_cur >> 3;

    FLIP_BIT(out_buf, afl->stage_cur);

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s FLIP_BIT1-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif

    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

    FLIP_BIT(out_buf, afl->stage_cur);

    /* While flipping the least significant bit in every byte, pull of an extra
       trick to detect possible syntax tokens. In essence, the idea is that if
       you have a binary blob like this:

       xxxxxxxxIHDRxxxxxxxx

       ...and changing the leading and trailing bytes causes variable or no
       changes in program flow, but touching any character in the "IHDR" string
       always produces the same, distinctive path, it's highly likely that
       "IHDR" is an atomically-checked magic value of special significance to
       the fuzzed format.

       We do this here, rather than as a separate stage, because it's a nice
       way to keep the operation approximately "free" (i.e., no extra execs).

       Empirically, performing the check when flipping the least significant bit
       is advantageous, compared to doing it at the time of more disruptive
       changes, where the program flow may be affected in more violent ways.

       The caveat is that we won't generate dictionaries in the -d mode or -S
       mode - but that's probably a fair trade-off.

       This won't work particularly well with paths that exhibit variable
       behavior, but fails gracefully, so we'll carry out the checks anyway.

      */

    if (!afl->non_instrumented_mode && (afl->stage_cur & 7) == 7) {

      u64 cksum = hash64(afl->fsrv.trace_bits, afl->fsrv.map_size, HASH_CONST);

      if (afl->stage_cur == afl->stage_max - 1 && cksum == prev_cksum) {

        /* If at end of file and we are still collecting a string, grab the
           final character and force output. */

        if (a_len < MAX_AUTO_EXTRA) {

          a_collect[a_len] = out_buf[afl->stage_cur >> 3];

        }

        ++a_len;

        if (a_len >= MIN_AUTO_EXTRA && a_len <= MAX_AUTO_EXTRA) {

          maybe_add_auto(afl, a_collect, a_len);

        }

      } else if (cksum != prev_cksum) {

        /* Otherwise, if the checksum has changed, see if we have something
           worthwhile queued up, and collect that if the answer is yes. */

        if (a_len >= MIN_AUTO_EXTRA && a_len <= MAX_AUTO_EXTRA) {

          maybe_add_auto(afl, a_collect, a_len);

        }

        a_len = 0;
        prev_cksum = cksum;

      }

      /* Continue collecting string, but only if the bit flip actually made
         any difference - we don't want no-op tokens. */

      if (cksum != afl->queue_cur->exec_cksum) {

        if (a_len < MAX_AUTO_EXTRA) {

          a_collect[a_len] = out_buf[afl->stage_cur >> 3];

        }

        ++a_len;

      }

    }

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP1] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP1] += afl->stage_max;

  /* Two walking bits. */

  afl->stage_name = "bitflip 2/1";
  afl->stage_short = "flip2";
  afl->stage_max = (len << 3) - 1;

  orig_hit_cnt = new_hit_cnt;

  for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max; ++afl->stage_cur) {

    afl->stage_cur_byte = afl->stage_cur >> 3;

    FLIP_BIT(out_buf, afl->stage_cur);
    FLIP_BIT(out_buf, afl->stage_cur + 1);

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s FLIP_BIT2-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif

    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

    FLIP_BIT(out_buf, afl->stage_cur);
    FLIP_BIT(out_buf, afl->stage_cur + 1);

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP2] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP2] += afl->stage_max;

  /* Four walking bits. */

  afl->stage_name = "bitflip 4/1";
  afl->stage_short = "flip4";
  afl->stage_max = (len << 3) - 3;

  orig_hit_cnt = new_hit_cnt;

  for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max; ++afl->stage_cur) {

    afl->stage_cur_byte = afl->stage_cur >> 3;

    FLIP_BIT(out_buf, afl->stage_cur);
    FLIP_BIT(out_buf, afl->stage_cur + 1);
    FLIP_BIT(out_buf, afl->stage_cur + 2);
    FLIP_BIT(out_buf, afl->stage_cur + 3);

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s FLIP_BIT4-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif

    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

    FLIP_BIT(out_buf, afl->stage_cur);
    FLIP_BIT(out_buf, afl->stage_cur + 1);
    FLIP_BIT(out_buf, afl->stage_cur + 2);
    FLIP_BIT(out_buf, afl->stage_cur + 3);

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP4] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP4] += afl->stage_max;

  /* Effector map setup. These macros calculate:

     EFF_APOS      - position of a particular file offset in the map.
     EFF_ALEN      - length of a map with a particular number of bytes.
     EFF_SPAN_ALEN - map span for a sequence of bytes.

   */

#define EFF_APOS(_p) ((_p) >> EFF_MAP_SCALE2)
#define EFF_REM(_x) ((_x) & ((1 << EFF_MAP_SCALE2) - 1))
#define EFF_ALEN(_l) (EFF_APOS(_l) + !!EFF_REM(_l))
#define EFF_SPAN_ALEN(_p, _l) (EFF_APOS((_p) + (_l)-1) - EFF_APOS(_p) + 1)

  /* Initialize effector map for the next step (see comments below). Always
     flag first and last byte as doing something. */

  eff_map = afl_realloc(AFL_BUF_PARAM(eff), EFF_ALEN(len));
  if (unlikely(!eff_map)) { PFATAL("alloc"); }
  eff_map[0] = 1;

  if (EFF_APOS(len - 1) != 0) {

    eff_map[EFF_APOS(len - 1)] = 1;
    ++eff_cnt;

  }

  /* Walking byte. */

  afl->stage_name = "bitflip 8/8";
  afl->stage_short = "flip8";
  afl->stage_max = len;

  orig_hit_cnt = new_hit_cnt;

  for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max; ++afl->stage_cur) {

    afl->stage_cur_byte = afl->stage_cur;

    out_buf[afl->stage_cur] ^= 0xFF;

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s FLIP_BIT8-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif

    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

    /* We also use this stage to pull off a simple trick: we identify
       bytes that seem to have no effect on the current execution path
       even when fully flipped - and we skip them during more expensive
       deterministic stages, such as arithmetics or known ints. */

    if (!eff_map[EFF_APOS(afl->stage_cur)]) {

      u64 cksum;

      /* If in non-instrumented mode or if the file is very short, just flag
         everything without wasting time on checksums. */

      if (!afl->non_instrumented_mode && len >= EFF_MIN_LEN) {

        cksum = hash64(afl->fsrv.trace_bits, afl->fsrv.map_size, HASH_CONST);

      } else {

        cksum = ~afl->queue_cur->exec_cksum;

      }

      if (cksum != afl->queue_cur->exec_cksum) {

        eff_map[EFF_APOS(afl->stage_cur)] = 1;
        ++eff_cnt;

      }

    }

    out_buf[afl->stage_cur] ^= 0xFF;

  }

  /* If the effector map is more than EFF_MAX_PERC dense, just flag the
     whole thing as worth fuzzing, since we wouldn't be saving much time
     anyway. */

  if (eff_cnt != (u32)EFF_ALEN(len) &&
      eff_cnt * 100 / EFF_ALEN(len) > EFF_MAX_PERC) {

    memset(eff_map, 1, EFF_ALEN(len));

    afl->blocks_eff_select += EFF_ALEN(len);

  } else {

    afl->blocks_eff_select += eff_cnt;

  }

  afl->blocks_eff_total += EFF_ALEN(len);

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP8] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP8] += afl->stage_max;

  /* Two walking bytes. */

  if (len < 2) { goto skip_bitflip; }

  afl->stage_name = "bitflip 16/8";
  afl->stage_short = "flip16";
  afl->stage_cur = 0;
  afl->stage_max = len - 1;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < len - 1; ++i) {

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)]) {

      --afl->stage_max;
      continue;

    }

    afl->stage_cur_byte = i;

    *(u16 *)(out_buf + i) ^= 0xFFFF;

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s FLIP_BIT16-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif

    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
    ++afl->stage_cur;

    *(u16 *)(out_buf + i) ^= 0xFFFF;

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP16] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP16] += afl->stage_max;

  if (len < 4) { goto skip_bitflip; }

  /* Four walking bytes. */

  afl->stage_name = "bitflip 32/8";
  afl->stage_short = "flip32";
  afl->stage_cur = 0;
  afl->stage_max = len - 3;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < len - 3; ++i) {

    /* Let's consult the effector map... */
    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)] &&
        !eff_map[EFF_APOS(i + 2)] && !eff_map[EFF_APOS(i + 3)]) {

      --afl->stage_max;
      continue;

    }

    afl->stage_cur_byte = i;

    *(u32 *)(out_buf + i) ^= 0xFFFFFFFF;

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s FLIP_BIT32-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif

    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
    ++afl->stage_cur;

    *(u32 *)(out_buf + i) ^= 0xFFFFFFFF;

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP32] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP32] += afl->stage_max;

skip_bitflip:

  if (afl->no_arith) { goto skip_arith; }

  /**********************
   * ARITHMETIC INC/DEC *
   **********************/

  /* 8-bit arithmetics. */

  afl->stage_name = "arith 8/8";
  afl->stage_short = "arith8";
  afl->stage_cur = 0;
  afl->stage_max = 2 * len * ARITH_MAX;

  afl->stage_val_type = STAGE_VAL_LE;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < (u32)len; ++i) {

    u8 orig = out_buf[i];

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)]) {

      afl->stage_max -= 2 * ARITH_MAX;
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 1; j <= ARITH_MAX; ++j) {

      u8 r = orig ^ (orig + j);

      /* Do arithmetic operations only if the result couldn't be a product
         of a bitflip. */

      if (!could_be_bitflip(r)) {

        afl->stage_cur_val = j;
        out_buf[i] = orig + j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s ARITH8+-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      r = orig ^ (orig - j);

      if (!could_be_bitflip(r)) {

        afl->stage_cur_val = -j;
        out_buf[i] = orig - j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s ARITH8--%u-%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      out_buf[i] = orig;

    }

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_ARITH8] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_ARITH8] += afl->stage_max;

  /* 16-bit arithmetics, both endians. */

  if (len < 2) { goto skip_arith; }

  afl->stage_name = "arith 16/8";
  afl->stage_short = "arith16";
  afl->stage_cur = 0;
  afl->stage_max = 4 * (len - 1) * ARITH_MAX;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < (u32)len - 1; ++i) {

    u16 orig = *(u16 *)(out_buf + i);

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)]) {

      afl->stage_max -= 4 * ARITH_MAX;
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 1; j <= ARITH_MAX; ++j) {

      u16 r1 = orig ^ (orig + j), r2 = orig ^ (orig - j),
          r3 = orig ^ SWAP16(SWAP16(orig) + j),
          r4 = orig ^ SWAP16(SWAP16(orig) - j);

      /* Try little endian addition and subtraction first. Do it only
         if the operation would affect more than one byte (hence the
         & 0xff overflow checks) and if it couldn't be a product of
         a bitflip. */

      afl->stage_val_type = STAGE_VAL_LE;

      if ((orig & 0xff) + j > 0xff && !could_be_bitflip(r1)) {

        afl->stage_cur_val = j;
        *(u16 *)(out_buf + i) = orig + j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s ARITH16+-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((orig & 0xff) < j && !could_be_bitflip(r2)) {

        afl->stage_cur_val = -j;
        *(u16 *)(out_buf + i) = orig - j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s ARITH16--%u-%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      /* Big endian comes next. Same deal. */

      afl->stage_val_type = STAGE_VAL_BE;

      if ((orig >> 8) + j > 0xff && !could_be_bitflip(r3)) {

        afl->stage_cur_val = j;
        *(u16 *)(out_buf + i) = SWAP16(SWAP16(orig) + j);

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s ARITH16+BE-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((orig >> 8) < j && !could_be_bitflip(r4)) {

        afl->stage_cur_val = -j;
        *(u16 *)(out_buf + i) = SWAP16(SWAP16(orig) - j);

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s ARITH16_BE-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      *(u16 *)(out_buf + i) = orig;

    }

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_ARITH16] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_ARITH16] += afl->stage_max;

  /* 32-bit arithmetics, both endians. */

  if (len < 4) { goto skip_arith; }

  afl->stage_name = "arith 32/8";
  afl->stage_short = "arith32";
  afl->stage_cur = 0;
  afl->stage_max = 4 * (len - 3) * ARITH_MAX;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < (u32)len - 3; ++i) {

    u32 orig = *(u32 *)(out_buf + i);

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)] &&
        !eff_map[EFF_APOS(i + 2)] && !eff_map[EFF_APOS(i + 3)]) {

      afl->stage_max -= 4 * ARITH_MAX;
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 1; j <= ARITH_MAX; ++j) {

      u32 r1 = orig ^ (orig + j), r2 = orig ^ (orig - j),
          r3 = orig ^ SWAP32(SWAP32(orig) + j),
          r4 = orig ^ SWAP32(SWAP32(orig) - j);

      /* Little endian first. Same deal as with 16-bit: we only want to
         try if the operation would have effect on more than two bytes. */

      afl->stage_val_type = STAGE_VAL_LE;

      if ((orig & 0xffff) + j > 0xffff && !could_be_bitflip(r1)) {

        afl->stage_cur_val = j;
        *(u32 *)(out_buf + i) = orig + j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s ARITH32+-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((orig & 0xffff) < (u32)j && !could_be_bitflip(r2)) {

        afl->stage_cur_val = -j;
        *(u32 *)(out_buf + i) = orig - j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s ARITH32_-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      /* Big endian next. */

      afl->stage_val_type = STAGE_VAL_BE;

      if ((SWAP32(orig) & 0xffff) + j > 0xffff && !could_be_bitflip(r3)) {

        afl->stage_cur_val = j;
        *(u32 *)(out_buf + i) = SWAP32(SWAP32(orig) + j);

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s ARITH32+BE-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((SWAP32(orig) & 0xffff) < (u32)j && !could_be_bitflip(r4)) {

        afl->stage_cur_val = -j;
        *(u32 *)(out_buf + i) = SWAP32(SWAP32(orig) - j);

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s ARITH32_BE-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      *(u32 *)(out_buf + i) = orig;

    }

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_ARITH32] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_ARITH32] += afl->stage_max;

skip_arith:

  /**********************
   * INTERESTING VALUES *
   **********************/

  afl->stage_name = "interest 8/8";
  afl->stage_short = "int8";
  afl->stage_cur = 0;
  afl->stage_max = len * sizeof(interesting_8);

  afl->stage_val_type = STAGE_VAL_LE;

  orig_hit_cnt = new_hit_cnt;

  /* Setting 8-bit integers. */

  for (i = 0; i < (u32)len; ++i) {

    u8 orig = out_buf[i];

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)]) {

      afl->stage_max -= sizeof(interesting_8);
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 0; j < (u32)sizeof(interesting_8); ++j) {

      /* Skip if the value could be a product of bitflips or arithmetics. */

      if (could_be_bitflip(orig ^ (u8)interesting_8[j]) ||
          could_be_arith(orig, (u8)interesting_8[j], 1)) {

        --afl->stage_max;
        continue;

      }

      afl->stage_cur_val = interesting_8[j];
      out_buf[i] = interesting_8[j];

#ifdef INTROSPECTION
      snprintf(afl->mutation, sizeof(afl->mutation), "%s INTERESTING8_%u_%u",
               afl->queue_cur->fname, i, j);
#endif

      if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

      out_buf[i] = orig;
      ++afl->stage_cur;

    }

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_INTEREST8] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_INTEREST8] += afl->stage_max;

  /* Setting 16-bit integers, both endians. */

  if (afl->no_arith || len < 2) { goto skip_interest; }

  afl->stage_name = "interest 16/8";
  afl->stage_short = "int16";
  afl->stage_cur = 0;
  afl->stage_max = 2 * (len - 1) * (sizeof(interesting_16) >> 1);

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < len - 1; ++i) {

    u16 orig = *(u16 *)(out_buf + i);

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)]) {

      afl->stage_max -= sizeof(interesting_16);
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 0; j < sizeof(interesting_16) / 2; ++j) {

      afl->stage_cur_val = interesting_16[j];

      /* Skip if this could be a product of a bitflip, arithmetics,
         or single-byte interesting value insertion. */

      if (!could_be_bitflip(orig ^ (u16)interesting_16[j]) &&
          !could_be_arith(orig, (u16)interesting_16[j], 2) &&
          !could_be_interest(orig, (u16)interesting_16[j], 2, 0)) {

        afl->stage_val_type = STAGE_VAL_LE;

        *(u16 *)(out_buf + i) = interesting_16[j];

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s INTERESTING16_%u_%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((u16)interesting_16[j] != SWAP16(interesting_16[j]) &&
          !could_be_bitflip(orig ^ SWAP16(interesting_16[j])) &&
          !could_be_arith(orig, SWAP16(interesting_16[j]), 2) &&
          !could_be_interest(orig, SWAP16(interesting_16[j]), 2, 1)) {

        afl->stage_val_type = STAGE_VAL_BE;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation),
                 "%s INTERESTING16BE_%u_%u", afl->queue_cur->fname, i, j);
#endif

        *(u16 *)(out_buf + i) = SWAP16(interesting_16[j]);
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

    }

    *(u16 *)(out_buf + i) = orig;

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_INTEREST16] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_INTEREST16] += afl->stage_max;

  if (len < 4) { goto skip_interest; }

  /* Setting 32-bit integers, both endians. */

  afl->stage_name = "interest 32/8";
  afl->stage_short = "int32";
  afl->stage_cur = 0;
  afl->stage_max = 2 * (len - 3) * (sizeof(interesting_32) >> 2);

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < len - 3; i++) {

    u32 orig = *(u32 *)(out_buf + i);

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)] &&
        !eff_map[EFF_APOS(i + 2)] && !eff_map[EFF_APOS(i + 3)]) {

      afl->stage_max -= sizeof(interesting_32) >> 1;
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 0; j < sizeof(interesting_32) / 4; ++j) {

      afl->stage_cur_val = interesting_32[j];

      /* Skip if this could be a product of a bitflip, arithmetics,
         or word interesting value insertion. */

      if (!could_be_bitflip(orig ^ (u32)interesting_32[j]) &&
          !could_be_arith(orig, interesting_32[j], 4) &&
          !could_be_interest(orig, interesting_32[j], 4, 0)) {

        afl->stage_val_type = STAGE_VAL_LE;

        *(u32 *)(out_buf + i) = interesting_32[j];

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s INTERESTING32_%u_%u",
                 afl->queue_cur->fname, i, j);
#endif

        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((u32)interesting_32[j] != SWAP32(interesting_32[j]) &&
          !could_be_bitflip(orig ^ SWAP32(interesting_32[j])) &&
          !could_be_arith(orig, SWAP32(interesting_32[j]), 4) &&
          !could_be_interest(orig, SWAP32(interesting_32[j]), 4, 1)) {

        afl->stage_val_type = STAGE_VAL_BE;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation),
                 "%s INTERESTING32BE_%u_%u", afl->queue_cur->fname, i, j);
#endif

        *(u32 *)(out_buf + i) = SWAP32(interesting_32[j]);
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

    }

    *(u32 *)(out_buf + i) = orig;

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_INTEREST32] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_INTEREST32] += afl->stage_max;

skip_interest:

  /********************
   * DICTIONARY STUFF *
   ********************/

  if (!afl->extras_cnt) { goto skip_user_extras; }

  /* Overwrite with user-supplied extras. */

  afl->stage_name = "user extras (over)";
  afl->stage_short = "ext_UO";
  afl->stage_cur = 0;
  afl->stage_max = afl->extras_cnt * len;

  afl->stage_val_type = STAGE_VAL_NONE;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < (u32)len; ++i) {

    u32 last_len = 0;

    afl->stage_cur_byte = i;

    /* Extras are sorted by size, from smallest to largest. This means
       that we don't have to worry about restoring the buffer in
       between writes at a particular offset determined by the outer
       loop. */

    for (j = 0; j < afl->extras_cnt; ++j) {

      /* Skip extras probabilistically if afl->extras_cnt > AFL_MAX_DET_EXTRAS.
         Also skip them if there's no room to insert the payload, if the token
         is redundant, or if its entire span has no bytes set in the effector
         map. */

      if ((afl->extras_cnt > afl->max_det_extras &&
           rand_below(afl, afl->extras_cnt) >= afl->max_det_extras) ||
          afl->extras[j].len > len - i ||
          !memcmp(afl->extras[j].data, out_buf + i, afl->extras[j].len) ||
          !memchr(eff_map + EFF_APOS(i), 1,
                  EFF_SPAN_ALEN(i, afl->extras[j].len))) {

        --afl->stage_max;
        continue;

      }

      last_len = afl->extras[j].len;
      memcpy(out_buf + i, afl->extras[j].data, last_len);

#ifdef INTROSPECTION
      snprintf(afl->mutation, sizeof(afl->mutation),
               "%s EXTRAS_overwrite-%u-%u", afl->queue_cur->fname, i, j);
#endif

      if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

      ++afl->stage_cur;

    }

    /* Restore all the clobbered memory. */
    memcpy(out_buf + i, in_buf + i, last_len);

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_EXTRAS_UO] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_EXTRAS_UO] += afl->stage_max;

  /* Insertion of user-supplied extras. */

  afl->stage_name = "user extras (insert)";
  afl->stage_short = "ext_UI";
  afl->stage_cur = 0;
  afl->stage_max = afl->extras_cnt * (len + 1);

  orig_hit_cnt = new_hit_cnt;

  ex_tmp = afl_realloc(AFL_BUF_PARAM(ex), len + MAX_DICT_FILE);
  if (unlikely(!ex_tmp)) { PFATAL("alloc"); }

  for (i = 0; i <= (u32)len; ++i) {

    afl->stage_cur_byte = i;

    for (j = 0; j < afl->extras_cnt; ++j) {

      if (len + afl->extras[j].len > MAX_FILE) {

        --afl->stage_max;
        continue;

      }

      /* Insert token */
      memcpy(ex_tmp + i, afl->extras[j].data, afl->extras[j].len);

      /* Copy tail */
      memcpy(ex_tmp + i + afl->extras[j].len, out_buf + i, len - i);

#ifdef INTROSPECTION
      snprintf(afl->mutation, sizeof(afl->mutation), "%s EXTRAS_insert-%u-%u",
               afl->queue_cur->fname, i, j);
#endif

      if (common_fuzz_stuff(afl, ex_tmp, len + afl->extras[j].len)) {

        goto abandon_entry;

      }

      ++afl->stage_cur;

    }

    /* Copy head */
    ex_tmp[i] = out_buf[i];

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_EXTRAS_UI] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_EXTRAS_UI] += afl->stage_max;

skip_user_extras:

  if (!afl->a_extras_cnt) { goto skip_extras; }

  afl->stage_name = "auto extras (over)";
  afl->stage_short = "ext_AO";
  afl->stage_cur = 0;
  afl->stage_max = MIN(afl->a_extras_cnt, (u32)USE_AUTO_EXTRAS) * len;

  afl->stage_val_type = STAGE_VAL_NONE;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < (u32)len; ++i) {

    u32 last_len = 0;

    afl->stage_cur_byte = i;

    u32 min_extra_len = MIN(afl->a_extras_cnt, (u32)USE_AUTO_EXTRAS);
    for (j = 0; j < min_extra_len; ++j) {

      /* See the comment in the earlier code; extras are sorted by size. */

      if (afl->a_extras[j].len > len - i ||
          !memcmp(afl->a_extras[j].data, out_buf + i, afl->a_extras[j].len) ||
          !memchr(eff_map + EFF_APOS(i), 1,
                  EFF_SPAN_ALEN(i, afl->a_extras[j].len))) {

        --afl->stage_max;
        continue;

      }

      last_len = afl->a_extras[j].len;
      memcpy(out_buf + i, afl->a_extras[j].data, last_len);

#ifdef INTROSPECTION
      snprintf(afl->mutation, sizeof(afl->mutation),
               "%s AUTO_EXTRAS_overwrite-%u-%u", afl->queue_cur->fname, i, j);
#endif

      if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

      ++afl->stage_cur;

    }

    /* Restore all the clobbered memory. */
    memcpy(out_buf + i, in_buf + i, last_len);

  }

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_EXTRAS_AO] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_EXTRAS_AO] += afl->stage_max;

skip_extras:

  /* If we made this to here without jumping to havoc_stage or abandon_entry,
     we're properly done with deterministic steps and can mark it as such
     in the .state/ directory. */

  if (!afl->queue_cur->passed_det) { mark_as_det_done(afl, afl->queue_cur); }

custom_mutator_stage:
  /*******************
   * CUSTOM MUTATORS *
   *******************/

  if (likely(!afl->custom_mutators_count)) { goto havoc_stage; }

  afl->stage_name = "custom mutator";
  afl->stage_short = "custom";
  afl->stage_max = HAVOC_CYCLES * perf_score / afl->havoc_div / 100;
  afl->stage_val_type = STAGE_VAL_NONE;
  bool has_custom_fuzz = false;

  if (afl->stage_max < HAVOC_MIN) { afl->stage_max = HAVOC_MIN; }

  const u32 max_seed_size = MAX_FILE, saved_max = afl->stage_max;

  orig_hit_cnt = afl->queued_items + afl->saved_crashes;

#ifdef INTROSPECTION
  afl->mutation[0] = 0;
#endif

  LIST_FOREACH(&afl->custom_mutator_list, struct custom_mutator, {

    if (el->afl_custom_fuzz) {

      afl->current_custom_fuzz = el;

      if (el->afl_custom_fuzz_count) {

        afl->stage_max = el->afl_custom_fuzz_count(el->data, out_buf, len);

      } else {

        afl->stage_max = saved_max;

      }

      has_custom_fuzz = true;

      afl->stage_short = el->name_short;

      if (afl->stage_max) {

        for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max;
             ++afl->stage_cur) {

          struct queue_entry *target = NULL;
          u32                 tid;
          u8 *                new_buf = NULL;
          u32                 target_len = 0;

          /* check if splicing makes sense yet (enough entries) */
          if (likely(afl->ready_for_splicing_count > 1)) {

            /* Pick a random other queue entry for passing to external API
               that has the necessary length */

            do {

              tid = rand_below(afl, afl->queued_items);

            } while (unlikely(tid == afl->current_entry ||

                              afl->queue_buf[tid]->len < 4));

            target = afl->queue_buf[tid];
            afl->splicing_with = tid;

            /* Read the additional testcase into a new buffer. */
            new_buf = queue_testcase_get(afl, target);
            target_len = target->len;

          }

          u8 *mutated_buf = NULL;

          size_t mutated_size =
              el->afl_custom_fuzz(el->data, out_buf, len, &mutated_buf, new_buf,
                                  target_len, max_seed_size);

          if (unlikely(!mutated_buf)) {

            FATAL("Error in custom_fuzz. Size returned: %zu", mutated_size);

          }

          if (mutated_size > 0) {

            if (common_fuzz_stuff(afl, mutated_buf, (u32)mutated_size)) {

              goto abandon_entry;

            }

            if (!el->afl_custom_fuzz_count) {

              /* If we're finding new stuff, let's run for a bit longer, limits
                permitting. */

              if (afl->queued_items != havoc_queued) {

                if (perf_score <= afl->havoc_max_mult * 100) {

                  afl->stage_max *= 2;
                  perf_score *= 2;

                }

                havoc_queued = afl->queued_items;

              }

            }

          }

          /* `(afl->)out_buf` may have been changed by the call to custom_fuzz
           */
          /* TODO: Only do this when `mutated_buf` == `out_buf`? Branch vs
           * Memcpy.
           */
          memcpy(out_buf, in_buf, len);

        }

      }

    }

  });

  afl->current_custom_fuzz = NULL;

  if (!has_custom_fuzz) goto havoc_stage;

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_CUSTOM_MUTATOR] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_CUSTOM_MUTATOR] += afl->stage_max;

  if (likely(afl->custom_only)) {

    /* Skip other stages */
    ret_val = 0;
    goto abandon_entry;

  }

  /****************
   * RANDOM HAVOC *
   ****************/

havoc_stage:

  afl->stage_cur_byte = -1;

  /* The havoc stage mutation code is also invoked when splicing files; if the
     splice_cycle variable is set, generate different descriptions and such. */

  if (!splice_cycle) {

    afl->stage_name = "havoc";
    afl->stage_short = "havoc";
    afl->stage_max = (doing_det ? HAVOC_CYCLES_INIT : HAVOC_CYCLES) *
                     perf_score / afl->havoc_div / 100;

  } else {

    perf_score = orig_perf;

    snprintf(afl->stage_name_buf, STAGE_BUF_SIZE, "splice %u", splice_cycle);
    afl->stage_name = afl->stage_name_buf;
    afl->stage_short = "splice";
    afl->stage_max = SPLICE_HAVOC * perf_score / afl->havoc_div / 100;

  }

  if (afl->stage_max < HAVOC_MIN) { afl->stage_max = HAVOC_MIN; }

  temp_len = len;

  orig_hit_cnt = afl->queued_items + afl->saved_crashes;

  havoc_queued = afl->queued_items;

  if (afl->custom_mutators_count) {

    LIST_FOREACH(&afl->custom_mutator_list, struct custom_mutator, {

      if (el->stacked_custom && el->afl_custom_havoc_mutation_probability) {

        el->stacked_custom_prob =
            el->afl_custom_havoc_mutation_probability(el->data);
        if (el->stacked_custom_prob > 100) {

          FATAL(
              "The probability returned by "
              "afl_custom_havoc_mutation_propability "
              "has to be in the range 0-100.");

        }

      }

    });

  }

  /* We essentially just do several thousand runs (depending on perf_score)
     where we take the input file and make random stacked tweaks. */

#define MAX_HAVOC_ENTRY 64
#define MUTATE_ASCII_DICT 64

  u32 r_max, r;

  r_max = (MAX_HAVOC_ENTRY + 1) + (afl->extras_cnt ? 4 : 0) +
          (afl->a_extras_cnt
               ? (unlikely(afl->cmplog_binary && afl->queue_cur->is_ascii)
                      ? MUTATE_ASCII_DICT
                      : 4)
               : 0);

  if (unlikely(afl->expand_havoc && afl->ready_for_splicing_count > 1)) {

    /* add expensive havoc cases here, they are activated after a full
       cycle without finds happened */

    r_max += 4;

  }

  if (unlikely(get_cur_time() - afl->last_find_time > 5000 /* 5 seconds */ &&
               afl->ready_for_splicing_count > 1)) {

    /* add expensive havoc cases here if there is no findings in the last 5s */

    r_max += 4;

  }

  afl->write_flag = 1;
  u8 using_feature_mode = 0;
  u32 cur_time = ((afl->prev_run_time + get_cur_time() - afl->start_time) / 1000);
  double per_exec_global = 1.0 * afl->plot_prev_ed / cur_time;
  if(cur_time > 1200) afl->time_to_use_length_mutator = 1;
  else afl->time_to_use_length_mutator = 0;  
  u32 mini_pos = temp_len;

  u8 history_able = 0;
  u32 history_mini_pos;
  u8 new_able = 0;
  u32 new_mini_pos;
  if(afl->history_mode && afl->queue_cur->ancestor_seed && afl->from_splicing == 0 && afl->queue_cur->vec_update_time){
    generate_mutation_sequence(afl);
    if(afl->history_mutation_sequence_idx){
      history_able = 1;
      history_mini_pos = temp_len;
      for(u32 e = 0;e < afl->history_mutation_sequence_idx;e++){
        if(history_mini_pos > afl->history_mutation_sequence[e]) history_mini_pos = afl->history_mutation_sequence[e];
      }
    }

    if(afl->distribution) free(afl->distribution);
    afl->distribution = (double *)malloc(sizeof(double) * afl->history_mutation_sequence_idx);
    memset(afl->distribution, 0, sizeof(double) * afl->history_mutation_sequence_idx);
    afl->distribution_sum = 0;
    afl->distribution_analyzed = 0;
  }
  if(afl->new_mode && afl->queue_cur->related_num && afl->from_splicing == 0){
    generate_mutation_sequence_new_mode(afl);
    if(afl->new_mutation_sequence_idx){
      new_able = 1;

      new_mini_pos = temp_len;
      for(u32 e = 0;e < afl->new_mutation_sequence_idx;e++){
        if(new_mini_pos > afl->new_mutation_sequence[e]) new_mini_pos = afl->new_mutation_sequence[e];
      }
    }
  }  

  u8 history_mode;
  u8 new_mode;
  u8 random_mode;
  double weight_history;
  double weight_new;
  double weight_random;
  double history_line;
  double new_line;
  double random_line;
  for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max; ++afl->stage_cur) {
    {
      history_mode = 0;
      new_mode = 0;
      random_mode = 0;

      double decrease = 0;
      if(per_exec_global > 0 && afl->stats_avg_exec > 0 && per_exec_global >  2 * afl->stats_avg_exec){
        
        decrease = 1.0 * (per_exec_global - afl->stats_avg_exec) / per_exec_global;
        if(decrease > 0.3) decrease = 0.3;
      }

      if(history_able == 0 && new_able == 0){
        double average = 1.0 * afl->found_all / afl->exec_all;
        weight_random = 1.0 * afl->queue_cur->found_by_random / afl->queue_cur->exec_random;
        if(afl->queue_cur->initial_seed == 0 && weight_random < average * (0.7 + decrease)){
          break;
        } 
        random_mode = 1;
      }
      else if(history_able == 0 && new_able == 1){
        weight_new = 1.0 * afl->queue_cur->found_by_new / afl->queue_cur->exec_new;
        weight_random = 1.0 * afl->queue_cur->found_by_random / afl->queue_cur->exec_random;

        double average = 1.0 * afl->found_all / afl->exec_all;
        if(weight_new < average * (0.7 + decrease) && weight_random < average * (0.7 + decrease)){
          break;
        } 

        new_line = weight_new;
        random_line = new_line + weight_random;

        double tmp = ((double)rand()/RAND_MAX) * random_line;
        if(tmp < weight_new) new_mode = 1;
        else random_mode = 1;
      }else if(history_able == 1 && new_able == 0){
        weight_history = 1.0 * afl->queue_cur->found_by_history / afl->queue_cur->exec_history;
        weight_random = 1.0 * afl->queue_cur->found_by_random / afl->queue_cur->exec_random;

        double average = 1.0 * afl->found_all / afl->exec_all;
        if(weight_history < average * (0.7 + decrease) && weight_random < average * (0.7 + decrease)){
          break;
        } 

        history_line = weight_history;
        random_line = history_line + weight_random;

        double tmp = ((double)rand()/RAND_MAX) * random_line;
        if(tmp < weight_history) history_mode = 1;
        else random_mode = 1;
      }else if(history_able && new_able){
        weight_history = 1.0 * afl->queue_cur->found_by_history / afl->queue_cur->exec_history;
        weight_new = 1.0 * afl->queue_cur->found_by_new / afl->queue_cur->exec_new;
        weight_random = 1.0 * afl->queue_cur->found_by_random / afl->queue_cur->exec_random;

        double average = 1.0 * afl->found_all / afl->exec_all;
        if(weight_history < average * (0.7 + decrease) && weight_new < average * (0.7 + decrease) && weight_random < average * (0.7 + decrease)){
          break;
        } 

        history_line = weight_history;
        new_line = weight_history + weight_new;
        random_line = new_line + weight_random;

        double tmp = ((double)rand()/RAND_MAX) * random_line;
        if(tmp < weight_history) history_mode = 1;
        else if(tmp < weight_new) new_mode = 1;
        else random_mode = 1;
      }
    }

    if(history_mode){
      using_feature_mode = 1;
      afl->time_to_use_length_mutator = 0;
      mini_pos = history_mini_pos;

      afl->cur_mutation_sequence = afl->history_mutation_sequence;
      afl->cur_mutation_sequence_idx = afl->history_mutation_sequence_idx;
    }else if(new_mode){
      using_feature_mode = 1;
      afl->time_to_use_length_mutator = 0;
      mini_pos = new_mini_pos;

      afl->cur_mutation_sequence = afl->new_mutation_sequence;
      afl->cur_mutation_sequence_idx = afl->new_mutation_sequence_idx;
    }else if(random_mode){
      using_feature_mode = 0;
    }else{
      printf("can not find correrspnding mode\n");
      exit(0);
    }
    
    afl->use_splice_mutator = 0;

    u32 use_stacking = 1 << (1 + rand_below(afl, afl->havoc_stack_pow2));

    afl->stage_cur_val = use_stacking;

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s HAVOC-%u",
             afl->queue_cur->fname, use_stacking);
#endif

    afl->splice_num = 0;
    if(using_feature_mode && history_mode){
      afl->record_flag = 1;
    }else{
      afl->record_flag = 0;
    }

    u8 buf_changed = 0;
    for (i = 0; i < use_stacking; ++i) {
      u32 pos_tmp = 0;
      u32 tmp = 0;

      if (afl->custom_mutators_count) {

        LIST_FOREACH(&afl->custom_mutator_list, struct custom_mutator, {

          if (el->stacked_custom &&
              rand_below(afl, 100) < el->stacked_custom_prob) {

            u8 *   custom_havoc_buf = NULL;
            size_t new_len = el->afl_custom_havoc_mutation(
                el->data, out_buf, temp_len, &custom_havoc_buf, MAX_FILE);
            if (unlikely(!custom_havoc_buf)) {

              FATAL("Error in custom_havoc (return %zu)", new_len);

            }

            if (likely(new_len > 0 && custom_havoc_buf)) {

              temp_len = new_len;
              if (out_buf != custom_havoc_buf) {

                out_buf = afl_realloc(AFL_BUF_PARAM(out), temp_len);
                if (unlikely(!afl->out_buf)) { PFATAL("alloc"); }
                memcpy(out_buf, custom_havoc_buf, temp_len);

              }

            }

          }

        });

      }

      if(afl->time_to_use_length_mutator == 0){
        r = rand_below(afl, 47);
      }else{
        r = rand_below(afl, r_max);
      }
      
      switch (r) {

        case 0 ... 3: {

          /* Flip a single bit somewhere. Spooky! */

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " FLIP_BIT1");
          strcat(afl->mutation, afl->m_tmp);
#endif

          if(using_feature_mode && history_mode){
            pos_tmp = select_position_based_on_distribution(afl);
            tmp = (pos_tmp << 3) + rand_below(afl, 8);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            tmp = (pos_tmp << 3) + rand_below(afl, 8);
          }else{
            tmp = rand_below(afl, temp_len << 3);
          }
          FLIP_BIT(out_buf, tmp);
          buf_changed = 1;
          break;

        }

        case 4 ... 7: {

          /* Set byte to interesting value. */

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " INTERESTING8");
          strcat(afl->mutation, afl->m_tmp);
#endif
          if(using_feature_mode && history_mode){
            pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }else{
            pos_tmp = rand_below(afl, temp_len);
          }
          out_buf[pos_tmp] =
              interesting_8[rand_below(afl, sizeof(interesting_8))];
          buf_changed = 1;
          break;

        }

        case 8 ... 9: {

          /* Set word to interesting value, little endian. */

          if (temp_len < 2) { break; }

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " INTERESTING16");
          strcat(afl->mutation, afl->m_tmp);
#endif
          if(using_feature_mode && history_mode && mini_pos < temp_len - 1){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 1)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 1){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 1)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 1);
          *(u16 *)(out_buf + pos_tmp) =
              interesting_16[rand_below(afl, sizeof(interesting_16) >> 1)];

          buf_changed = 1;

          break;

        }

        case 10 ... 11: {

          /* Set word to interesting value, big endian. */

          if (temp_len < 2) { break; }

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " INTERESTING16BE");
          strcat(afl->mutation, afl->m_tmp);
#endif
          if(using_feature_mode && history_mode && mini_pos < temp_len - 1){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 1)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 1){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 1)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 1);
          *(u16 *)(out_buf + pos_tmp) = SWAP16(
              interesting_16[rand_below(afl, sizeof(interesting_16) >> 1)]);

          buf_changed = 1;
          break;

        }

        case 12 ... 13: {

          /* Set dword to interesting value, little endian. */

          if (temp_len < 4) { break; }

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " INTERESTING32");
          strcat(afl->mutation, afl->m_tmp);
#endif
          if(using_feature_mode && history_mode && mini_pos < temp_len - 3){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 3)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 3){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 3)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 3);
          *(u32 *)(out_buf + pos_tmp) =
              interesting_32[rand_below(afl, sizeof(interesting_32) >> 2)];

          buf_changed = 1;
          break;

        }

        case 14 ... 15: {

          /* Set dword to interesting value, big endian. */

          if (temp_len < 4) { break; }

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " INTERESTING32BE");
          strcat(afl->mutation, afl->m_tmp);
#endif
          if(using_feature_mode && history_mode && mini_pos < temp_len - 3){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 3)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 3){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 3)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 3);
          *(u32 *)(out_buf + pos_tmp) = SWAP32(
              interesting_32[rand_below(afl, sizeof(interesting_32) >> 2)]);

          buf_changed = 1;
          break;

        }

        case 16 ... 19: {

          /* Randomly subtract from byte. */

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH8_");
          strcat(afl->mutation, afl->m_tmp);
#endif
          if(using_feature_mode && history_mode){
            pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }else{
            pos_tmp = rand_below(afl, temp_len);
          }
          out_buf[pos_tmp] -= 1 + rand_below(afl, ARITH_MAX);
          buf_changed = 1;
          break;

        }

        case 20 ... 23: {

          /* Randomly add to byte. */

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH8+");
          strcat(afl->mutation, afl->m_tmp);
#endif
          if(using_feature_mode && history_mode){
            pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }else{
            pos_tmp = rand_below(afl, temp_len);
          }
          out_buf[pos_tmp] += 1 + rand_below(afl, ARITH_MAX);
          buf_changed = 1;
          break;

        }

        case 24 ... 25: {

          /* Randomly subtract from word, little endian. */

          if (temp_len < 2) { break; }

          if(using_feature_mode && history_mode && mini_pos < temp_len - 1){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 1)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 1){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 1)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 1);
          u32 pos = pos_tmp;

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH16_-%u", pos);
          strcat(afl->mutation, afl->m_tmp);
#endif
          *(u16 *)(out_buf + pos) -= 1 + rand_below(afl, ARITH_MAX);

          buf_changed = 1;
          break;

        }

        case 26 ... 27: {

          /* Randomly subtract from word, big endian. */

          if (temp_len < 2) { break; }

          if(using_feature_mode && history_mode && mini_pos < temp_len - 1){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 1)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 1){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 1)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 1);
          u32 pos = pos_tmp;
          u16 num = 1 + rand_below(afl, ARITH_MAX);

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH16_BE-%u_%u", pos,
                   num);
          strcat(afl->mutation, afl->m_tmp);
#endif
          *(u16 *)(out_buf + pos) =
              SWAP16(SWAP16(*(u16 *)(out_buf + pos)) - num);

          buf_changed = 1;
          break;

        }

        case 28 ... 29: {

          /* Randomly add to word, little endian. */

          if (temp_len < 2) { break; }
          if(using_feature_mode && history_mode && mini_pos < temp_len - 1){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 1)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 1){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 1)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 1);
          u32 pos = pos_tmp;

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH16+-%u", pos);
          strcat(afl->mutation, afl->m_tmp);
#endif
          *(u16 *)(out_buf + pos) += 1 + rand_below(afl, ARITH_MAX);

          buf_changed = 1;
          break;

        }

        case 30 ... 31: {

          /* Randomly add to word, big endian. */

          if (temp_len < 2) { break; }
          
          if(using_feature_mode && history_mode && mini_pos < temp_len - 1){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 1)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 1){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 1)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 1);
          u32 pos = pos_tmp;
          u16 num = 1 + rand_below(afl, ARITH_MAX);

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH16+BE-%u_%u", pos,
                   num);
          strcat(afl->mutation, afl->m_tmp);
#endif
          *(u16 *)(out_buf + pos) =
              SWAP16(SWAP16(*(u16 *)(out_buf + pos)) + num);

          buf_changed = 1;
          break;

        }

        case 32 ... 33: {

          /* Randomly subtract from dword, little endian. */

          if (temp_len < 4) { break; }

          if(using_feature_mode && history_mode && mini_pos < temp_len - 3){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 3)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 3){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 3)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 3);
          u32 pos = pos_tmp;

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH32_-%u", pos);
          strcat(afl->mutation, afl->m_tmp);
#endif
          *(u32 *)(out_buf + pos) -= 1 + rand_below(afl, ARITH_MAX);

          buf_changed = 1;
          break;

        }

        case 34 ... 35: {

          /* Randomly subtract from dword, big endian. */

          if (temp_len < 4) { break; }

          if(using_feature_mode && history_mode && mini_pos < temp_len - 3){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 3)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 3){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 3)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 3);
          u32 pos = pos_tmp;
          u32 num = 1 + rand_below(afl, ARITH_MAX);

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH32_BE-%u-%u", pos,
                   num);
          strcat(afl->mutation, afl->m_tmp);
#endif
          *(u32 *)(out_buf + pos) =
              SWAP32(SWAP32(*(u32 *)(out_buf + pos)) - num);

          buf_changed = 1;
          break;

        }

        case 36 ... 37: {

          /* Randomly add to dword, little endian. */

          if (temp_len < 4) { break; }

          if(using_feature_mode && history_mode && mini_pos < temp_len - 3){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 3)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 3){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 3)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 3);
          u32 pos = pos_tmp;

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH32+-%u", pos);
          strcat(afl->mutation, afl->m_tmp);
#endif
          *(u32 *)(out_buf + pos) += 1 + rand_below(afl, ARITH_MAX);

          buf_changed = 1;
          break;

        }

        case 38 ... 39: {

          /* Randomly add to dword, big endian. */

          if (temp_len < 4) { break; }

          if(using_feature_mode && history_mode && mini_pos < temp_len - 3){
            pos_tmp = select_position_based_on_distribution(afl);
            while(pos_tmp >= temp_len - 3)
              pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - 3){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(pos_tmp >= temp_len - 3)
              pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            pos_tmp = rand_below(afl, temp_len - 3);
          u32 pos = pos_tmp;
          u32 num = 1 + rand_below(afl, ARITH_MAX);

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH32+BE-%u-%u", pos,
                   num);
          strcat(afl->mutation, afl->m_tmp);
#endif
          *(u32 *)(out_buf + pos) =
              SWAP32(SWAP32(*(u32 *)(out_buf + pos)) + num);

          buf_changed = 1;
          break;

        }

        case 40 ... 43: {

          /* Just set a random byte to a random value. Because,
             why not. We use XOR with 1-255 to eliminate the
             possibility of a no-op. */

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " RAND8");
          strcat(afl->mutation, afl->m_tmp);
#endif
          if(using_feature_mode && history_mode){
            pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }else{
            pos_tmp = rand_below(afl, temp_len);
          }
          out_buf[pos_tmp] ^= 1 + rand_below(afl, 255);
          buf_changed = 1;
          break;

        }

        case 53 ... 55: {
          if(afl->time_to_use_length_mutator == 0) break;

          if (temp_len + HAVOC_BLK_XL < MAX_FILE) {

            afl->use_splice_mutator = 1;
            // printf("use_splice_mutator\n");

            /* Clone bytes. */

            u32 clone_len = choose_block_len(afl, temp_len);
            u32 clone_from = rand_below(afl, temp_len - clone_len + 1);
            u32 clone_to = rand_below(afl, temp_len);

#ifdef INTROSPECTION
            snprintf(afl->m_tmp, sizeof(afl->m_tmp), " CLONE-%s-%u-%u-%u",
                     "clone", clone_from, clone_to, clone_len);
            strcat(afl->mutation, afl->m_tmp);
#endif
            u8 *new_buf =
                afl_realloc(AFL_BUF_PARAM(out_scratch), temp_len + clone_len);
            if (unlikely(!new_buf)) { PFATAL("alloc"); }

            /* Head */

            memcpy(new_buf, out_buf, clone_to);

            /* Inserted part */

            memcpy(new_buf + clone_to, out_buf + clone_from, clone_len);

            /* Tail */
            memcpy(new_buf + clone_to + clone_len, out_buf + clone_to,
                   temp_len - clone_to);

            out_buf = new_buf;
            afl_swap_bufs(AFL_BUF_PARAM(out), AFL_BUF_PARAM(out_scratch));
            temp_len += clone_len;

            if(afl->splice_num < 512){
              afl->splice_stack[afl->splice_num][0] = 1;
              afl->splice_stack[afl->splice_num][1] = clone_to;
              afl->splice_stack[afl->splice_num][2] = clone_len;
              afl->splice_num++;
            }

          }

          buf_changed = 1;
          break;

        }

        case 56: {

          if(afl->time_to_use_length_mutator == 0) break;

          if (temp_len + HAVOC_BLK_XL < MAX_FILE) {

            afl->use_splice_mutator = 1;
            /* Insert a block of constant bytes (25%). */

            u32 clone_len = choose_block_len(afl, HAVOC_BLK_XL);
            u32 clone_to = rand_below(afl, temp_len);

#ifdef INTROSPECTION
            snprintf(afl->m_tmp, sizeof(afl->m_tmp), " CLONE-%s-%u-%u",
                     "insert", clone_to, clone_len);
            strcat(afl->mutation, afl->m_tmp);
#endif
            u8 *new_buf =
                afl_realloc(AFL_BUF_PARAM(out_scratch), temp_len + clone_len);
            if (unlikely(!new_buf)) { PFATAL("alloc"); }

            /* Head */

            memcpy(new_buf, out_buf, clone_to);

            /* Inserted part */

            memset(new_buf + clone_to,
                   rand_below(afl, 2) ? rand_below(afl, 256)
                                      : out_buf[rand_below(afl, temp_len)],
                   clone_len);

            /* Tail */
            memcpy(new_buf + clone_to + clone_len, out_buf + clone_to,
                   temp_len - clone_to);

            out_buf = new_buf;
            afl_swap_bufs(AFL_BUF_PARAM(out), AFL_BUF_PARAM(out_scratch));
            temp_len += clone_len;

            if(afl->splice_num < 512){
              afl->splice_stack[afl->splice_num][0] = 1;
              afl->splice_stack[afl->splice_num][1] = clone_to;
              afl->splice_stack[afl->splice_num][2] = clone_len;
              afl->splice_num++;
            }

          }
          buf_changed = 1;
          break;

        }

        case 47 ... 49: {
          if(afl->time_to_use_length_mutator == 0) break;

          /* Overwrite bytes with a randomly selected chunk bytes. */

          if (temp_len < 2) { break; }

          u32 copy_len = choose_block_len(afl, temp_len - 1);
          u32 copy_from = rand_below(afl, temp_len - copy_len + 1);
          u32 copy_to;
          if(using_feature_mode && history_mode && mini_pos < temp_len - copy_len + 1){
            copy_to = select_position_based_on_distribution(afl);
            while(copy_to >= temp_len - copy_len + 1)
              copy_to = select_position_based_on_distribution(afl);
            update(afl, copy_to);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - copy_len + 1){
            copy_to = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(copy_to >= temp_len - copy_len + 1)
              copy_to = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            copy_to = rand_below(afl, temp_len - copy_len + 1);

          if (likely(copy_from != copy_to)) {

#ifdef INTROSPECTION
            snprintf(afl->m_tmp, sizeof(afl->m_tmp), " OVERWRITE_COPY-%u-%u-%u",
                     copy_from, copy_to, copy_len);
            strcat(afl->mutation, afl->m_tmp);
#endif
            memmove(out_buf + copy_to, out_buf + copy_from, copy_len);

          }

          buf_changed = 1;
          break;

        }

        case 50: {
          if(afl->time_to_use_length_mutator == 0) break;

          /* Overwrite bytes with fixed bytes. */

          if (temp_len < 2) { break; }

          u32 copy_len = choose_block_len(afl, temp_len - 1);
          u32 copy_to;
          if(using_feature_mode && history_mode && mini_pos < temp_len - copy_len + 1){
            copy_to = select_position_based_on_distribution(afl);
            while(copy_to >= temp_len - copy_len + 1)
              copy_to = select_position_based_on_distribution(afl);
            update(afl, copy_to);
          }
          else if(using_feature_mode && new_mode && mini_pos < temp_len - copy_len + 1){
            copy_to = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            while(copy_to >= temp_len - copy_len + 1)
              copy_to = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }
          else
            copy_to = rand_below(afl, temp_len - copy_len + 1);

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " OVERWRITE_FIXED-%u-%u",
                   copy_to, copy_len);
          strcat(afl->mutation, afl->m_tmp);
#endif
          memset(out_buf + copy_to,
                 rand_below(afl, 2) ? rand_below(afl, 256)
                                    : out_buf[rand_below(afl, temp_len)],
                 copy_len);

          buf_changed = 1;
          break;

        }

        case 44: {
          if(using_feature_mode && history_mode){
            pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }else{
            pos_tmp = rand_below(afl, temp_len);
          }

          /* Increase byte by 1. */

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ADDBYTE_");
          strcat(afl->mutation, afl->m_tmp);
#endif
          out_buf[pos_tmp]++;
          buf_changed = 1;
          break;

        }

        case 45: {

          /* Decrease byte by 1. */

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " SUBBYTE_");
          strcat(afl->mutation, afl->m_tmp);
#endif
          if(using_feature_mode && history_mode){
            pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }else{
            pos_tmp = rand_below(afl, temp_len);
          }
          out_buf[pos_tmp]++;
          buf_changed = 1;
          break;

        }

        case 46: {

          /* Flip byte. */

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " FLIP8_");
          strcat(afl->mutation, afl->m_tmp);
#endif
          if(using_feature_mode && history_mode){
            pos_tmp = select_position_based_on_distribution(afl);
            update(afl, pos_tmp);
          }
          else if(using_feature_mode && new_mode){
            pos_tmp = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }else{
            pos_tmp = rand_below(afl, temp_len);
          }
          out_buf[pos_tmp] ^= 0xff;
          buf_changed = 1;
          break;

        }

        case 51 ... 52: {
          if(afl->time_to_use_length_mutator == 0) break;

          if (temp_len < 4) { break; }

          /* Switch bytes. */

          u32 to_end, switch_to, switch_len, switch_from;
          // switch_from = rand_below(afl, temp_len);
          if(using_feature_mode && history_mode){
            switch_from = select_position_based_on_distribution(afl);
            update(afl, switch_from);
          }
          else if(using_feature_mode && new_mode){
            switch_from = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
          }else{
            switch_from = rand_below(afl, temp_len); //
          }
          do {

            // switch_to = rand_below(afl, temp_len);
            if(using_feature_mode && history_mode){
              switch_to = select_position_based_on_distribution(afl);
              update(afl, switch_to);
            }
            else if(using_feature_mode && new_mode){
              switch_to = afl->cur_mutation_sequence[rand_below(afl, afl->cur_mutation_sequence_idx)];
            }else{
              switch_to = rand_below(afl, temp_len); //
            }

          } while (switch_from == switch_to);

          if (switch_from < switch_to) {

            switch_len = switch_to - switch_from;
            to_end = temp_len - switch_to;

          } else {

            switch_len = switch_from - switch_to;
            to_end = temp_len - switch_from;

          }

          switch_len = choose_block_len(afl, MIN(switch_len, to_end));

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " SWITCH-%s-%u-%u-%u",
                   "switch", switch_from, switch_to, switch_len);
          strcat(afl->mutation, afl->m_tmp);
#endif
          u8 *new_buf = afl_realloc(AFL_BUF_PARAM(out_scratch), switch_len);
          if (unlikely(!new_buf)) { PFATAL("alloc"); }

          /* Backup */

          memcpy(new_buf, out_buf + switch_from, switch_len);

          /* Switch 1 */

          memcpy(out_buf + switch_from, out_buf + switch_to, switch_len);

          /* Switch 2 */

          memcpy(out_buf + switch_to, new_buf, switch_len);

          buf_changed = 1;
          break;

        }

        // MAX_HAVOC_ENTRY = 64
        case 57 ... MAX_HAVOC_ENTRY: {

          if(afl->time_to_use_length_mutator == 0) break;
          afl->use_splice_mutator = 1;
          /* Delete bytes. */

          if (temp_len < 2) { break; }

          /* Don't delete too much. */

          u32 del_len = choose_block_len(afl, temp_len - 1);
          u32 del_from = rand_below(afl, temp_len - del_len + 1);

#ifdef INTROSPECTION
          snprintf(afl->m_tmp, sizeof(afl->m_tmp), " DEL-%u-%u", del_from,
                   del_len);
          strcat(afl->mutation, afl->m_tmp);
#endif
          if(afl->splice_num < 512 && del_len < 1500){
            afl->splice_stack[afl->splice_num][0] = 2;
            afl->splice_stack[afl->splice_num][1] = del_from;
            afl->splice_stack[afl->splice_num][2] = del_len;
            memcpy((u8*)(&(afl->splice_stack[afl->splice_num][3])), out_buf + del_from, del_len);
            afl->splice_num++;
          }else break;
          memmove(out_buf + del_from, out_buf + del_from + del_len,
                  temp_len - del_from - del_len);

          temp_len -= del_len;

          buf_changed = 1;
          break;

        }

        default:

          if(afl->time_to_use_length_mutator == 0) break;
          afl->use_splice_mutator = 2;
          r -= (MAX_HAVOC_ENTRY + 1);

          if (afl->extras_cnt) {

            if (r < 2) {

              /* Use the dictionary. */

              u32 use_extra = rand_below(afl, afl->extras_cnt);
              u32 extra_len = afl->extras[use_extra].len;

              if (extra_len > temp_len) { break; }

              u32 insert_at = rand_below(afl, temp_len - extra_len + 1);
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " EXTRA_OVERWRITE-%u-%u",
                       insert_at, extra_len);
              strcat(afl->mutation, afl->m_tmp);
#endif
              memcpy(out_buf + insert_at, afl->extras[use_extra].data,
                     extra_len);

              break;

            } else if (r < 4) {

              u32 use_extra = rand_below(afl, afl->extras_cnt);
              u32 extra_len = afl->extras[use_extra].len;
              if (temp_len + extra_len >= MAX_FILE) { break; }

              u8 *ptr = afl->extras[use_extra].data;
              u32 insert_at = rand_below(afl, temp_len + 1);
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " EXTRA_INSERT-%u-%u",
                       insert_at, extra_len);
              strcat(afl->mutation, afl->m_tmp);
#endif

              out_buf = afl_realloc(AFL_BUF_PARAM(out), temp_len + extra_len);
              if (unlikely(!out_buf)) { PFATAL("alloc"); }

              /* Tail */
              memmove(out_buf + insert_at + extra_len, out_buf + insert_at,
                      temp_len - insert_at);

              /* Inserted part */
              memcpy(out_buf + insert_at, ptr, extra_len);
              temp_len += extra_len;

              break;

            } else {

              r -= 4;

            }

          }

          if (afl->a_extras_cnt) {

            u32 r_cmp = 2;

            if (unlikely(afl->cmplog_binary && afl->queue_cur->is_ascii)) {

              r_cmp = MUTATE_ASCII_DICT >> 1;

            }

            if (r < r_cmp) {

              /* Use the dictionary. */

              u32 use_extra = rand_below(afl, afl->a_extras_cnt);
              u32 extra_len = afl->a_extras[use_extra].len;

              if (extra_len > temp_len) { break; }

              u32 insert_at = rand_below(afl, temp_len - extra_len + 1);
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp),
                       " AUTO_EXTRA_OVERWRITE-%u-%u", insert_at, extra_len);
              strcat(afl->mutation, afl->m_tmp);
#endif
              memcpy(out_buf + insert_at, afl->a_extras[use_extra].data,
                     extra_len);

              break;

            } else if (r < (r_cmp << 1)) {

              u32 use_extra = rand_below(afl, afl->a_extras_cnt);
              u32 extra_len = afl->a_extras[use_extra].len;
              if (temp_len + extra_len >= MAX_FILE) { break; }

              u8 *ptr = afl->a_extras[use_extra].data;
              u32 insert_at = rand_below(afl, temp_len + 1);
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp),
                       " AUTO_EXTRA_INSERT-%u-%u", insert_at, extra_len);
              strcat(afl->mutation, afl->m_tmp);
#endif

              out_buf = afl_realloc(AFL_BUF_PARAM(out), temp_len + extra_len);
              if (unlikely(!out_buf)) { PFATAL("alloc"); }

              /* Tail */
              memmove(out_buf + insert_at + extra_len, out_buf + insert_at,
                      temp_len - insert_at);

              /* Inserted part */
              memcpy(out_buf + insert_at, ptr, extra_len);
              temp_len += extra_len;

              break;

            } else {

              r -= (r_cmp << 1);

            }

          }

          /* Splicing otherwise if we are still here.
             Overwrite bytes with a randomly selected chunk from another
             testcase or insert that chunk. */

          /* Pick a random queue entry and seek to it. */

          u32 tid;
          do {

            tid = rand_below(afl, afl->queued_items);

          } while (tid == afl->current_entry || afl->queue_buf[tid]->len < 4);

          /* Get the testcase for splicing. */
          struct queue_entry *target = afl->queue_buf[tid];
          u32                 new_len = target->len;
          u8 *                new_buf = queue_testcase_get(afl, target);

          if ((temp_len >= 2 && r % 2) || temp_len + HAVOC_BLK_XL >= MAX_FILE) {

            /* overwrite mode */

            u32 copy_from, copy_to, copy_len;

            copy_len = choose_block_len(afl, new_len - 1);
            if (copy_len > temp_len) copy_len = temp_len;

            copy_from = rand_below(afl, new_len - copy_len + 1);
            copy_to = rand_below(afl, temp_len - copy_len + 1);

#ifdef INTROSPECTION
            snprintf(afl->m_tmp, sizeof(afl->m_tmp),
                     " SPLICE_OVERWRITE-%u-%u-%u-%s", copy_from, copy_to,
                     copy_len, target->fname);
            strcat(afl->mutation, afl->m_tmp);
#endif
            memmove(out_buf + copy_to, new_buf + copy_from, copy_len);

          } else {

            /* insert mode */

            u32 clone_from, clone_to, clone_len;

            clone_len = choose_block_len(afl, new_len);
            clone_from = rand_below(afl, new_len - clone_len + 1);
            clone_to = rand_below(afl, temp_len + 1);

            u8 *temp_buf = afl_realloc(AFL_BUF_PARAM(out_scratch),
                                       temp_len + clone_len + 1);
            if (unlikely(!temp_buf)) { PFATAL("alloc"); }

#ifdef INTROSPECTION
            snprintf(afl->m_tmp, sizeof(afl->m_tmp),
                     " SPLICE_INSERT-%u-%u-%u-%s", clone_from, clone_to,
                     clone_len, target->fname);
            strcat(afl->mutation, afl->m_tmp);
#endif
            /* Head */

            memcpy(temp_buf, out_buf, clone_to);

            /* Inserted part */

            memcpy(temp_buf + clone_to, new_buf + clone_from, clone_len);

            /* Tail */
            memcpy(temp_buf + clone_to + clone_len, out_buf + clone_to,
                   temp_len - clone_to);

            out_buf = temp_buf;
            afl_swap_bufs(AFL_BUF_PARAM(out), AFL_BUF_PARAM(out_scratch));
            temp_len += clone_len;

          }

          buf_changed = 1;
          break;

          // end of default

      }

    }


    if (common_fuzz_stuff(afl, out_buf, temp_len)) { goto abandon_entry; }

    stat_analysis(afl, temp_len, out_buf, in_buf, len, history_mode);
    afl->use_splice_mutator = 0;
    /* out_buf might have been mangled a bit, so let's restore it to its
       original size and shape. */

    out_buf = afl_realloc(AFL_BUF_PARAM(out), len);
    if (unlikely(!out_buf)) { PFATAL("alloc"); }
    temp_len = len;
    memcpy(out_buf, in_buf, len);

    /* If we're finding new stuff, let's run for a bit longer, limits
       permitting. */
    afl->exec_all++;
    if(history_mode){
      afl->queue_cur->exec_history++;
      afl->exec_history_all++;
    } 
    else if(new_mode){
      afl->queue_cur->exec_new++;
      afl->exec_new_all++;
    }
    else if(random_mode){
      afl->queue_cur->exec_random++;
      afl->exec_random_all++;
    }
    else{
      printf("Mode sheduler met some problems\n");
      exit(0);
    }

    if (afl->queued_items != havoc_queued) {

      afl->found_all++;
      if(history_mode){
        afl->queue_cur->found_by_history++;
        afl->found_by_history_all++;
      }
      else if(new_mode){
        afl->queue_cur->found_by_new++;
        afl->found_by_new_all++;
      }
      else if(random_mode){
        afl->queue_cur->found_by_random++;
        afl->found_by_random_all++;
      }
      else{
        printf("Mode sheduler met some problems\n");
        exit(0);
      }

      if (perf_score <= afl->havoc_max_mult * 100) {

        afl->stage_max *= 2;
        perf_score *= 2;

      }

      havoc_queued = afl->queued_items;

    }

  }


  if(afl->dataset_size){ 
    float max_reward = 0;
    float min_reward = 999999999999999;
    for(u32 i = 0; i < afl->queue_cur->len;i++){
      if(afl->hit_nums[i]){
        if(afl->dataset_reward[i]/afl->hit_nums[i] > max_reward) max_reward = afl->dataset_reward[i]/afl->hit_nums[i];
        else if(afl->dataset_reward[i]/afl->hit_nums[i] < min_reward) min_reward = afl->dataset_reward[i]/afl->hit_nums[i];
      }
    }
    if(max_reward != 0 && min_reward != 999999999999999 && max_reward != min_reward){
      for(u32 i = 0; i < afl->queue_cur->len;i++){
        if(afl->hit_nums[i]){
          afl->dataset_reward[i] = (afl->dataset_reward[i]/afl->hit_nums[i] - min_reward)/(max_reward - min_reward);
        }
      }
    }

    if(max_reward != min_reward){
        struct queue_entry * ancestor_node = afl->queue_cur->ancestor_seed;
        u32 cnt = 0;
        for(u32 i = 0;i < afl->queue_cur->len;i++){
          u32 ii = (afl->queue_cur->map)[i];
          if(ancestor_node->mutated_pos[ii].flag >= 1 && afl->hit_nums[i]){
            cnt++;
            Matrix* feature_vec_copy = Matrix_copy(afl->queue_cur->feature_vec);
            Matrix* feature_vec_T = M_T(feature_vec_copy);
            Matrix* Mul = M_mul(feature_vec_copy,feature_vec_T);
            Matrix* old = ancestor_node->mutated_pos[ii].A;
            ancestor_node->mutated_pos[ii].A = M_add_sub(1,old, -1,Mul);
            M_free(feature_vec_T);
            M_free(Mul);
            M_free(old);

            M_free(feature_vec_copy);
            feature_vec_copy = Matrix_copy(afl->queue_cur->feature_vec);
            Matrix* Mul_b = M_numul(feature_vec_copy, afl->dataset_reward[i]);
            Matrix* old_b = ancestor_node->mutated_pos[ii].b;
            ancestor_node->mutated_pos[ii].b = M_add_sub(1,old_b, -1,Mul_b);

            if(isinf(ancestor_node->mutated_pos[ii].b->data[0])){
              printf("====== %u -> b ======\n", i);
              printf("feature_vec_copy\n");
              M_print(feature_vec_copy);
              printf("dataset_reward:%f\n", afl->dataset_reward[i]);
              printf("Mul_b\n");
              M_print(Mul_b);
              printf("old_b\n");
              M_print(old_b);
              printf("ancestor_node->mutated_pos[ii].b\n");
              M_print(ancestor_node->mutated_pos[ii].b);
              exit(0);
            }

            M_free(Mul_b);
            M_free(old_b);
          }
        }
    }
  }

  afl->write_flag = 0;

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  if (!splice_cycle) {

    afl->stage_finds[STAGE_HAVOC] += new_hit_cnt - orig_hit_cnt;
    afl->stage_cycles[STAGE_HAVOC] += afl->stage_max;

  } else {

    afl->stage_finds[STAGE_SPLICE] += new_hit_cnt - orig_hit_cnt;
    afl->stage_cycles[STAGE_SPLICE] += afl->stage_max;

  }

  if(afl->from_splicing == 0){
    afl->dataset_size = 0;
  }
  

#ifndef IGNORE_FINDS

  /************
   * SPLICING *
   ************/

  /* This is a last-resort strategy triggered by a full round with no findings.
     It takes the current input file, randomly selects another input, and
     splices them together at some offset, then relies on the havoc
     code to mutate that blob. */

retry_splicing:

  if(((afl->prev_run_time + get_cur_time() - afl->start_time) / 1000) > 1200 && afl->queue_cycle <= 1){
    u32 tmp = rand_below(afl, 4);
    if(tmp == 1){
      afl->use_splicing = 1;
    }else{
      afl->use_splicing = 0;
    }
  }
  else if(afl->queue_cycle > 1){
    afl->use_splicing = 1;
  }else{
    afl->use_splicing = 0;
  }

  if (afl->use_splicing && splice_cycle++ < SPLICE_CYCLES &&
      afl->ready_for_splicing_count > 1 && afl->queue_cur->len >= 4) {

    afl->from_splicing = 1;
    struct queue_entry *target;
    u32                 tid, split_at;
    u8 *                new_buf;
    s32                 f_diff, l_diff;

    /* First of all, if we've modified in_buf for havoc, let's clean that
       up... */

    if (in_buf != orig_in) {

      in_buf = orig_in;
      len = afl->queue_cur->len;

    }

    /* Pick a random queue entry and seek to it. Don't splice with yourself. */

    do {

      tid = rand_below(afl, afl->queued_items);

    } while (tid == afl->current_entry || afl->queue_buf[tid]->len < 4);

    /* Get the testcase */
    afl->splicing_with = tid;
    target = afl->queue_buf[tid];
    new_buf = queue_testcase_get(afl, target);

    /* Find a suitable splicing location, somewhere between the first and
       the last differing byte. Bail out if the difference is just a single
       byte or so. */

    locate_diffs(in_buf, new_buf, MIN(len, (s64)target->len), &f_diff, &l_diff);

    if (f_diff < 0 || l_diff < 2 || f_diff == l_diff) { goto retry_splicing; }

    /* Split somewhere between the first and last differing byte. */

    split_at = f_diff + rand_below(afl, l_diff - f_diff);

    /* Do the thing. */

    len = target->len;
    afl->in_scratch_buf = afl_realloc(AFL_BUF_PARAM(in_scratch), len);
    memcpy(afl->in_scratch_buf, in_buf, split_at);
    memcpy(afl->in_scratch_buf + split_at, new_buf, len - split_at);
    in_buf = afl->in_scratch_buf;
    afl_swap_bufs(AFL_BUF_PARAM(in), AFL_BUF_PARAM(in_scratch));

    out_buf = afl_realloc(AFL_BUF_PARAM(out), len);
    if (unlikely(!out_buf)) { PFATAL("alloc"); }
    memcpy(out_buf, in_buf, len);

    goto custom_mutator_stage;

  }

#endif                                                     /* !IGNORE_FINDS */

  ret_val = 0;

/* we are through with this queue entry - for this iteration */
abandon_entry:

  afl->splicing_with = -1;

  /* Update afl->pending_not_fuzzed count if we made it through the calibration
     cycle and have not seen this entry before. */

  if (!afl->stop_soon && !afl->queue_cur->cal_failed &&
      !afl->queue_cur->was_fuzzed && !afl->queue_cur->disabled) {

    --afl->pending_not_fuzzed;
    afl->queue_cur->was_fuzzed = 1;
    afl->reinit_table = 1;
    if (afl->queue_cur->favored) { --afl->pending_favored; }

  }

  ++afl->queue_cur->fuzz_level;
  orig_in = NULL;
  return ret_val;

#undef FLIP_BIT

}

/* MOpt mode */
static u8 mopt_common_fuzzing(afl_state_t *afl, MOpt_globals_t MOpt_globals) {

  if (!MOpt_globals.is_pilot_mode) {

    if (swarm_num == 1) {

      afl->key_module = 2;
      return 0;

    }

  }

  u32 len, temp_len;
  u32 i;
  u32 j;
  u8 *in_buf, *out_buf, *orig_in, *ex_tmp, *eff_map = 0;
  u64 havoc_queued = 0, orig_hit_cnt, new_hit_cnt = 0, cur_ms_lv, prev_cksum;
  u32 splice_cycle = 0, perf_score = 100, orig_perf, eff_cnt = 1;

  u8 ret_val = 1, doing_det = 0;

  u8  a_collect[MAX_AUTO_EXTRA];
  u32 a_len = 0;

#ifdef IGNORE_FINDS

  /* In IGNORE_FINDS mode, skip any entries that weren't in the
     initial data set. */

  if (afl->queue_cur->depth > 1) return 1;

#else

  if (likely(afl->pending_favored)) {

    /* If we have any favored, non-fuzzed new arrivals in the queue,
       possibly skip to them at the expense of already-fuzzed or non-favored
       cases. */

    if ((afl->queue_cur->fuzz_level || !afl->queue_cur->favored) &&
        rand_below(afl, 100) < SKIP_TO_NEW_PROB) {

      return 1;

    }

  } else if (!afl->non_instrumented_mode && !afl->queue_cur->favored &&

             afl->queued_items > 10) {

    /* Otherwise, still possibly skip non-favored cases, albeit less often.
       The odds of skipping stuff are higher for already-fuzzed inputs and
       lower for never-fuzzed entries. */

    if (afl->queue_cycle > 1 && !afl->queue_cur->fuzz_level) {

      if (likely(rand_below(afl, 100) < SKIP_NFAV_NEW_PROB)) { return 1; }

    } else {

      if (likely(rand_below(afl, 100) < SKIP_NFAV_OLD_PROB)) { return 1; }

    }

  }

#endif                                                     /* ^IGNORE_FINDS */

  if (afl->not_on_tty) {

    ACTF("Fuzzing test case #%u (%u total, %llu crashes saved)...",
         afl->current_entry, afl->queued_items, afl->saved_crashes);
    fflush(stdout);

  }

  /* Map the test case into memory. */
  orig_in = in_buf = queue_testcase_get(afl, afl->queue_cur);
  len = afl->queue_cur->len;

  out_buf = afl_realloc(AFL_BUF_PARAM(out), len);
  if (unlikely(!out_buf)) { PFATAL("alloc"); }

  afl->subseq_tmouts = 0;

  afl->cur_depth = afl->queue_cur->depth;

  /*******************************************
   * CALIBRATION (only if failed earlier on) *
   *******************************************/

  if (unlikely(afl->queue_cur->cal_failed)) {

    u8 res = FSRV_RUN_TMOUT;

    if (afl->queue_cur->cal_failed < CAL_CHANCES) {

      afl->queue_cur->exec_cksum = 0;

      res =
          calibrate_case(afl, afl->queue_cur, in_buf, afl->queue_cycle - 1, 0);

      if (res == FSRV_RUN_ERROR) {

        FATAL("Unable to execute target application");

      }

    }

    if (afl->stop_soon || res != afl->crash_mode) {

      ++afl->cur_skipped_items;
      goto abandon_entry;

    }

  }

  /************
   * TRIMMING *
   ************/

  if (unlikely(!afl->non_instrumented_mode && !afl->queue_cur->trim_done &&
               !afl->disable_trim)) {

    u32 old_len = afl->queue_cur->len;

    u8 res = trim_case(afl, afl->queue_cur, in_buf);
    orig_in = in_buf = queue_testcase_get(afl, afl->queue_cur);

    if (unlikely(res == FSRV_RUN_ERROR)) {

      FATAL("Unable to execute target application");

    }

    if (unlikely(afl->stop_soon)) {

      ++afl->cur_skipped_items;
      goto abandon_entry;

    }

    /* Don't retry trimming, even if it failed. */

    afl->queue_cur->trim_done = 1;

    len = afl->queue_cur->len;

    /* maybe current entry is not ready for splicing anymore */
    if (unlikely(len <= 4 && old_len > 4)) --afl->ready_for_splicing_count;

  }

  memcpy(out_buf, in_buf, len);

  /*********************
   * PERFORMANCE SCORE *
   *********************/

  if (likely(!afl->old_seed_selection))
    orig_perf = perf_score = afl->queue_cur->perf_score;
  else
    orig_perf = perf_score = calculate_score(afl, afl->queue_cur);

  if (unlikely(perf_score <= 0 && afl->active_items > 1)) {

    goto abandon_entry;

  }

  if (unlikely(afl->shm.cmplog_mode &&
               afl->queue_cur->colorized < afl->cmplog_lvl &&
               (u32)len <= afl->cmplog_max_filesize)) {

    if (unlikely(len < 4)) {

      afl->queue_cur->colorized = CMPLOG_LVL_MAX;

    } else {

      if (afl->cmplog_lvl == 3 ||
          (afl->cmplog_lvl == 2 && afl->queue_cur->tc_ref) ||
          !(afl->fsrv.total_execs % afl->queued_items) ||
          get_cur_time() - afl->last_find_time > 300000) {  // 300 seconds

        if (input_to_state_stage(afl, in_buf, out_buf, len)) {

          goto abandon_entry;

        }

      }

    }

  }

  /* Go to pacemker fuzzing if MOpt is doing well */

  cur_ms_lv = get_cur_time();
  if (!(afl->key_puppet == 0 &&
        ((cur_ms_lv - afl->last_find_time < (u32)afl->limit_time_puppet) ||
         (afl->last_crash_time != 0 &&
          cur_ms_lv - afl->last_crash_time < (u32)afl->limit_time_puppet) ||
         afl->last_find_time == 0))) {

    afl->key_puppet = 1;
    goto pacemaker_fuzzing;

  }

  /* Skip right away if -d is given, if we have done deterministic fuzzing on
     this entry ourselves (was_fuzzed), or if it has gone through deterministic
     testing in earlier, resumed runs (passed_det). */

  if (likely(afl->skip_deterministic || afl->queue_cur->was_fuzzed ||
             afl->queue_cur->passed_det)) {

    goto havoc_stage;

  }

  /* Skip deterministic fuzzing if exec path checksum puts this out of scope
     for this main instance. */

  if (unlikely(afl->main_node_max &&
               (afl->queue_cur->exec_cksum % afl->main_node_max) !=
                   afl->main_node_id - 1)) {

    goto havoc_stage;

  }

  doing_det = 1;

  /*********************************************
   * SIMPLE BITFLIP (+dictionary construction) *
   *********************************************/

#define FLIP_BIT(_ar, _b)                   \
  do {                                      \
                                            \
    u8 *_arf = (u8 *)(_ar);                 \
    u32 _bf = (_b);                         \
    _arf[(_bf) >> 3] ^= (128 >> ((_bf)&7)); \
                                            \
  } while (0)

  /* Single walking bit. */

  afl->stage_short = "flip1";
  afl->stage_max = len << 3;
  afl->stage_name = "bitflip 1/1";

  afl->stage_val_type = STAGE_VAL_NONE;

  orig_hit_cnt = afl->queued_items + afl->saved_crashes;

  prev_cksum = afl->queue_cur->exec_cksum;

  for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max; ++afl->stage_cur) {

    afl->stage_cur_byte = afl->stage_cur >> 3;

    FLIP_BIT(out_buf, afl->stage_cur);

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_FLIP_BIT1-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif
    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

    FLIP_BIT(out_buf, afl->stage_cur);

    /* While flipping the least significant bit in every byte, pull of an extra
       trick to detect possible syntax tokens. In essence, the idea is that if
       you have a binary blob like this:

       xxxxxxxxIHDRxxxxxxxx

       ...and changing the leading and trailing bytes causes variable or no
       changes in program flow, but touching any character in the "IHDR" string
       always produces the same, distinctive path, it's highly likely that
       "IHDR" is an atomically-checked magic value of special significance to
       the fuzzed format.

       We do this here, rather than as a separate stage, because it's a nice
       way to keep the operation approximately "free" (i.e., no extra execs).

       Empirically, performing the check when flipping the least significant bit
       is advantageous, compared to doing it at the time of more disruptive
       changes, where the program flow may be affected in more violent ways.

       The caveat is that we won't generate dictionaries in the -d mode or -S
       mode - but that's probably a fair trade-off.

       This won't work particularly well with paths that exhibit variable
       behavior, but fails gracefully, so we'll carry out the checks anyway.

      */

    if (!afl->non_instrumented_mode && (afl->stage_cur & 7) == 7) {

      u64 cksum = hash64(afl->fsrv.trace_bits, afl->fsrv.map_size, HASH_CONST);

      if (afl->stage_cur == afl->stage_max - 1 && cksum == prev_cksum) {

        /* If at end of file and we are still collecting a string, grab the
           final character and force output. */

        if (a_len < MAX_AUTO_EXTRA) {

          a_collect[a_len] = out_buf[afl->stage_cur >> 3];

        }

        ++a_len;

        if (a_len >= MIN_AUTO_EXTRA && a_len <= MAX_AUTO_EXTRA) {

          maybe_add_auto(afl, a_collect, a_len);

        }

      } else if (cksum != prev_cksum) {

        /* Otherwise, if the checksum has changed, see if we have something
           worthwhile queued up, and collect that if the answer is yes. */

        if (a_len >= MIN_AUTO_EXTRA && a_len <= MAX_AUTO_EXTRA) {

          maybe_add_auto(afl, a_collect, a_len);

        }

        a_len = 0;
        prev_cksum = cksum;

      }

      /* Continue collecting string, but only if the bit flip actually made
         any difference - we don't want no-op tokens. */

      if (cksum != afl->queue_cur->exec_cksum) {

        if (a_len < MAX_AUTO_EXTRA) {

          a_collect[a_len] = out_buf[afl->stage_cur >> 3];

        }

        ++a_len;

      }

    }                                       /* if (afl->stage_cur & 7) == 7 */

  }                                                   /* for afl->stage_cur */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP1] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP1] += afl->stage_max;

  /* Two walking bits. */

  afl->stage_name = "bitflip 2/1";
  afl->stage_short = "flip2";
  afl->stage_max = (len << 3) - 1;

  orig_hit_cnt = new_hit_cnt;

  for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max; ++afl->stage_cur) {

    afl->stage_cur_byte = afl->stage_cur >> 3;

    FLIP_BIT(out_buf, afl->stage_cur);
    FLIP_BIT(out_buf, afl->stage_cur + 1);

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_FLIP_BIT2-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif
    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

    FLIP_BIT(out_buf, afl->stage_cur);
    FLIP_BIT(out_buf, afl->stage_cur + 1);

  }                                                   /* for afl->stage_cur */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP2] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP2] += afl->stage_max;

  /* Four walking bits. */

  afl->stage_name = "bitflip 4/1";
  afl->stage_short = "flip4";
  afl->stage_max = (len << 3) - 3;

  orig_hit_cnt = new_hit_cnt;

  for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max; ++afl->stage_cur) {

    afl->stage_cur_byte = afl->stage_cur >> 3;

    FLIP_BIT(out_buf, afl->stage_cur);
    FLIP_BIT(out_buf, afl->stage_cur + 1);
    FLIP_BIT(out_buf, afl->stage_cur + 2);
    FLIP_BIT(out_buf, afl->stage_cur + 3);

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_FLIP_BIT4-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif
    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

    FLIP_BIT(out_buf, afl->stage_cur);
    FLIP_BIT(out_buf, afl->stage_cur + 1);
    FLIP_BIT(out_buf, afl->stage_cur + 2);
    FLIP_BIT(out_buf, afl->stage_cur + 3);

  }                                                   /* for afl->stage_cur */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP4] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP4] += afl->stage_max;

  /* Effector map setup. These macros calculate:

     EFF_APOS      - position of a particular file offset in the map.
     EFF_ALEN      - length of a map with a particular number of bytes.
     EFF_SPAN_ALEN - map span for a sequence of bytes.

   */

#define EFF_APOS(_p) ((_p) >> EFF_MAP_SCALE2)
#define EFF_REM(_x) ((_x) & ((1 << EFF_MAP_SCALE2) - 1))
#define EFF_ALEN(_l) (EFF_APOS(_l) + !!EFF_REM(_l))
#define EFF_SPAN_ALEN(_p, _l) (EFF_APOS((_p) + (_l)-1) - EFF_APOS(_p) + 1)

  /* Initialize effector map for the next step (see comments below). Always
         flag first and last byte as doing something. */

  eff_map = afl_realloc(AFL_BUF_PARAM(eff), EFF_ALEN(len));
  if (unlikely(!eff_map)) { PFATAL("alloc"); }
  eff_map[0] = 1;

  if (EFF_APOS(len - 1) != 0) {

    eff_map[EFF_APOS(len - 1)] = 1;
    ++eff_cnt;

  }

  /* Walking byte. */

  afl->stage_name = "bitflip 8/8";
  afl->stage_short = "flip8";
  afl->stage_max = len;

  orig_hit_cnt = new_hit_cnt;

  for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max; ++afl->stage_cur) {

    afl->stage_cur_byte = afl->stage_cur;

    out_buf[afl->stage_cur] ^= 0xFF;

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_FLIP_BIT8-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif
    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

    /* We also use this stage to pull off a simple trick: we identify
       bytes that seem to have no effect on the current execution path
       even when fully flipped - and we skip them during more expensive
       deterministic stages, such as arithmetics or known ints. */

    if (!eff_map[EFF_APOS(afl->stage_cur)]) {

      u64 cksum;

      /* If in non-instrumented mode or if the file is very short, just flag
         everything without wasting time on checksums. */

      if (!afl->non_instrumented_mode && len >= EFF_MIN_LEN) {

        cksum = hash64(afl->fsrv.trace_bits, afl->fsrv.map_size, HASH_CONST);

      } else {

        cksum = ~afl->queue_cur->exec_cksum;

      }

      if (cksum != afl->queue_cur->exec_cksum) {

        eff_map[EFF_APOS(afl->stage_cur)] = 1;
        ++eff_cnt;

      }

    }

    out_buf[afl->stage_cur] ^= 0xFF;

  }                                                   /* for afl->stage_cur */

  /* If the effector map is more than EFF_MAX_PERC dense, just flag the
     whole thing as worth fuzzing, since we wouldn't be saving much time
     anyway. */

  if (eff_cnt != (u32)EFF_ALEN(len) &&
      eff_cnt * 100 / EFF_ALEN(len) > EFF_MAX_PERC) {

    memset(eff_map, 1, EFF_ALEN(len));

    afl->blocks_eff_select += EFF_ALEN(len);

  } else {

    afl->blocks_eff_select += eff_cnt;

  }

  afl->blocks_eff_total += EFF_ALEN(len);

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP8] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP8] += afl->stage_max;

  /* Two walking bytes. */

  if (len < 2) { goto skip_bitflip; }

  afl->stage_name = "bitflip 16/8";
  afl->stage_short = "flip16";
  afl->stage_cur = 0;
  afl->stage_max = len - 1;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < len - 1; ++i) {

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)]) {

      --afl->stage_max;
      continue;

    }

    afl->stage_cur_byte = i;

    *(u16 *)(out_buf + i) ^= 0xFFFF;

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_FLIP_BIT16-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif
    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
    ++afl->stage_cur;

    *(u16 *)(out_buf + i) ^= 0xFFFF;

  }                                                   /* for i = 0; i < len */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP16] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP16] += afl->stage_max;

  if (len < 4) { goto skip_bitflip; }

  /* Four walking bytes. */

  afl->stage_name = "bitflip 32/8";
  afl->stage_short = "flip32";
  afl->stage_cur = 0;
  afl->stage_max = len - 3;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < len - 3; ++i) {

    /* Let's consult the effector map... */
    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)] &&
        !eff_map[EFF_APOS(i + 2)] && !eff_map[EFF_APOS(i + 3)]) {

      --afl->stage_max;
      continue;

    }

    afl->stage_cur_byte = i;

    *(u32 *)(out_buf + i) ^= 0xFFFFFFFF;

#ifdef INTROSPECTION
    snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_FLIP_BIT32-%u",
             afl->queue_cur->fname, afl->stage_cur);
#endif
    if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
    ++afl->stage_cur;

    *(u32 *)(out_buf + i) ^= 0xFFFFFFFF;

  }                                               /* for i = 0; i < len - 3 */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_FLIP32] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_FLIP32] += afl->stage_max;

skip_bitflip:

  if (afl->no_arith) { goto skip_arith; }

  /**********************
   * ARITHMETIC INC/DEC *
   **********************/

  /* 8-bit arithmetics. */

  afl->stage_name = "arith 8/8";
  afl->stage_short = "arith8";
  afl->stage_cur = 0;
  afl->stage_max = 2 * len * ARITH_MAX;

  afl->stage_val_type = STAGE_VAL_LE;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < (u32)len; ++i) {

    u8 orig = out_buf[i];

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)]) {

      afl->stage_max -= 2 * ARITH_MAX;
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 1; j <= ARITH_MAX; ++j) {

      u8 r = orig ^ (orig + j);

      /* Do arithmetic operations only if the result couldn't be a product
         of a bitflip. */

      if (!could_be_bitflip(r)) {

        afl->stage_cur_val = j;
        out_buf[i] = orig + j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_ARITH8+-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      r = orig ^ (orig - j);

      if (!could_be_bitflip(r)) {

        afl->stage_cur_val = -j;
        out_buf[i] = orig - j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_ARITH8_-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      out_buf[i] = orig;

    }

  }                                                   /* for i = 0; i < len */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_ARITH8] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_ARITH8] += afl->stage_max;

  /* 16-bit arithmetics, both endians. */

  if (len < 2) { goto skip_arith; }

  afl->stage_name = "arith 16/8";
  afl->stage_short = "arith16";
  afl->stage_cur = 0;
  afl->stage_max = 4 * (len - 1) * ARITH_MAX;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < len - 1; ++i) {

    u16 orig = *(u16 *)(out_buf + i);

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)]) {

      afl->stage_max -= 4 * ARITH_MAX;
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 1; j <= ARITH_MAX; ++j) {

      u16 r1 = orig ^ (orig + j), r2 = orig ^ (orig - j),
          r3 = orig ^ SWAP16(SWAP16(orig) + j),
          r4 = orig ^ SWAP16(SWAP16(orig) - j);

      /* Try little endian addition and subtraction first. Do it only
         if the operation would affect more than one byte (hence the
         & 0xff overflow checks) and if it couldn't be a product of
         a bitflip. */

      afl->stage_val_type = STAGE_VAL_LE;

      if ((orig & 0xff) + j > 0xff && !could_be_bitflip(r1)) {

        afl->stage_cur_val = j;
        *(u16 *)(out_buf + i) = orig + j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_ARITH16+-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((orig & 0xff) < j && !could_be_bitflip(r2)) {

        afl->stage_cur_val = -j;
        *(u16 *)(out_buf + i) = orig - j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_ARITH16_-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      /* Big endian comes next. Same deal. */

      afl->stage_val_type = STAGE_VAL_BE;

      if ((orig >> 8) + j > 0xff && !could_be_bitflip(r3)) {

        afl->stage_cur_val = j;
        *(u16 *)(out_buf + i) = SWAP16(SWAP16(orig) + j);

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation),
                 "%s MOPT_ARITH16+BE-%u-%u", afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((orig >> 8) < j && !could_be_bitflip(r4)) {

        afl->stage_cur_val = -j;
        *(u16 *)(out_buf + i) = SWAP16(SWAP16(orig) - j);

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation),
                 "%s MOPT_ARITH16_BE+%u+%u", afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      *(u16 *)(out_buf + i) = orig;

    }

  }                                               /* for i = 0; i < len - 1 */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_ARITH16] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_ARITH16] += afl->stage_max;

  /* 32-bit arithmetics, both endians. */

  if (len < 4) { goto skip_arith; }

  afl->stage_name = "arith 32/8";
  afl->stage_short = "arith32";
  afl->stage_cur = 0;
  afl->stage_max = 4 * (len - 3) * ARITH_MAX;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < len - 3; ++i) {

    u32 orig = *(u32 *)(out_buf + i);

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)] &&
        !eff_map[EFF_APOS(i + 2)] && !eff_map[EFF_APOS(i + 3)]) {

      afl->stage_max -= 4 * ARITH_MAX;
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 1; j <= ARITH_MAX; ++j) {

      u32 r1 = orig ^ (orig + j), r2 = orig ^ (orig - j),
          r3 = orig ^ SWAP32(SWAP32(orig) + j),
          r4 = orig ^ SWAP32(SWAP32(orig) - j);

      /* Little endian first. Same deal as with 16-bit: we only want to
         try if the operation would have effect on more than two bytes. */

      afl->stage_val_type = STAGE_VAL_LE;

      if ((orig & 0xffff) + j > 0xffff && !could_be_bitflip(r1)) {

        afl->stage_cur_val = j;
        *(u32 *)(out_buf + i) = orig + j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_ARITH32+-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((orig & 0xffff) < j && !could_be_bitflip(r2)) {

        afl->stage_cur_val = -j;
        *(u32 *)(out_buf + i) = orig - j;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_ARITH32_-%u-%u",
                 afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      /* Big endian next. */

      afl->stage_val_type = STAGE_VAL_BE;

      if ((SWAP32(orig) & 0xffff) + j > 0xffff && !could_be_bitflip(r3)) {

        afl->stage_cur_val = j;
        *(u32 *)(out_buf + i) = SWAP32(SWAP32(orig) + j);

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation),
                 "%s MOPT_ARITH32+BE-%u-%u", afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((SWAP32(orig) & 0xffff) < j && !could_be_bitflip(r4)) {

        afl->stage_cur_val = -j;
        *(u32 *)(out_buf + i) = SWAP32(SWAP32(orig) - j);

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation),
                 "%s MOPT_ARITH32_BE-%u-%u", afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      *(u32 *)(out_buf + i) = orig;

    }

  }                                               /* for i = 0; i < len - 3 */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_ARITH32] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_ARITH32] += afl->stage_max;

skip_arith:

  /**********************
   * INTERESTING VALUES *
   **********************/

  afl->stage_name = "interest 8/8";
  afl->stage_short = "int8";
  afl->stage_cur = 0;
  afl->stage_max = len * sizeof(interesting_8);

  afl->stage_val_type = STAGE_VAL_LE;

  orig_hit_cnt = new_hit_cnt;

  /* Setting 8-bit integers. */

  for (i = 0; i < (u32)len; ++i) {

    u8 orig = out_buf[i];

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)]) {

      afl->stage_max -= sizeof(interesting_8);
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 0; j < sizeof(interesting_8); ++j) {

      /* Skip if the value could be a product of bitflips or arithmetics. */

      if (could_be_bitflip(orig ^ (u8)interesting_8[j]) ||
          could_be_arith(orig, (u8)interesting_8[j], 1)) {

        --afl->stage_max;
        continue;

      }

      afl->stage_cur_val = interesting_8[j];
      out_buf[i] = interesting_8[j];

#ifdef INTROSPECTION
      snprintf(afl->mutation, sizeof(afl->mutation),
               "%s MOPT_INTERESTING8-%u-%u", afl->queue_cur->fname, i, j);
#endif
      if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

      out_buf[i] = orig;
      ++afl->stage_cur;

    }

  }                                                   /* for i = 0; i < len */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_INTEREST8] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_INTEREST8] += afl->stage_max;

  /* Setting 16-bit integers, both endians. */

  if (afl->no_arith || len < 2) { goto skip_interest; }

  afl->stage_name = "interest 16/8";
  afl->stage_short = "int16";
  afl->stage_cur = 0;
  afl->stage_max = 2 * (len - 1) * (sizeof(interesting_16) >> 1);

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < len - 1; ++i) {

    u16 orig = *(u16 *)(out_buf + i);

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)]) {

      afl->stage_max -= sizeof(interesting_16);
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 0; j < sizeof(interesting_16) / 2; ++j) {

      afl->stage_cur_val = interesting_16[j];

      /* Skip if this could be a product of a bitflip, arithmetics,
         or single-byte interesting value insertion. */

      if (!could_be_bitflip(orig ^ (u16)interesting_16[j]) &&
          !could_be_arith(orig, (u16)interesting_16[j], 2) &&
          !could_be_interest(orig, (u16)interesting_16[j], 2, 0)) {

        afl->stage_val_type = STAGE_VAL_LE;

        *(u16 *)(out_buf + i) = interesting_16[j];

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation),
                 "%s MOPT_INTERESTING16-%u-%u", afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((u16)interesting_16[j] != SWAP16(interesting_16[j]) &&
          !could_be_bitflip(orig ^ SWAP16(interesting_16[j])) &&
          !could_be_arith(orig, SWAP16(interesting_16[j]), 2) &&
          !could_be_interest(orig, SWAP16(interesting_16[j]), 2, 1)) {

        afl->stage_val_type = STAGE_VAL_BE;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation),
                 "%s MOPT_INTERESTING16BE-%u-%u", afl->queue_cur->fname, i, j);
#endif
        *(u16 *)(out_buf + i) = SWAP16(interesting_16[j]);
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

    }

    *(u16 *)(out_buf + i) = orig;

  }                                               /* for i = 0; i < len - 1 */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_INTEREST16] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_INTEREST16] += afl->stage_max;

  if (len < 4) { goto skip_interest; }

  /* Setting 32-bit integers, both endians. */

  afl->stage_name = "interest 32/8";
  afl->stage_short = "int32";
  afl->stage_cur = 0;
  afl->stage_max = 2 * (len - 3) * (sizeof(interesting_32) >> 2);

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < len - 3; ++i) {

    u32 orig = *(u32 *)(out_buf + i);

    /* Let's consult the effector map... */

    if (!eff_map[EFF_APOS(i)] && !eff_map[EFF_APOS(i + 1)] &&
        !eff_map[EFF_APOS(i + 2)] && !eff_map[EFF_APOS(i + 3)]) {

      afl->stage_max -= sizeof(interesting_32) >> 1;
      continue;

    }

    afl->stage_cur_byte = i;

    for (j = 0; j < sizeof(interesting_32) / 4; ++j) {

      afl->stage_cur_val = interesting_32[j];

      /* Skip if this could be a product of a bitflip, arithmetics,
         or word interesting value insertion. */

      if (!could_be_bitflip(orig ^ (u32)interesting_32[j]) &&
          !could_be_arith(orig, interesting_32[j], 4) &&
          !could_be_interest(orig, interesting_32[j], 4, 0)) {

        afl->stage_val_type = STAGE_VAL_LE;

        *(u32 *)(out_buf + i) = interesting_32[j];

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation),
                 "%s MOPT_INTERESTING32-%u-%u", afl->queue_cur->fname, i, j);
#endif
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

      if ((u32)interesting_32[j] != SWAP32(interesting_32[j]) &&
          !could_be_bitflip(orig ^ SWAP32(interesting_32[j])) &&
          !could_be_arith(orig, SWAP32(interesting_32[j]), 4) &&
          !could_be_interest(orig, SWAP32(interesting_32[j]), 4, 1)) {

        afl->stage_val_type = STAGE_VAL_BE;

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation),
                 "%s MOPT_INTERESTING32BE-%u-%u", afl->queue_cur->fname, i, j);
#endif
        *(u32 *)(out_buf + i) = SWAP32(interesting_32[j]);
        if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }
        ++afl->stage_cur;

      } else {

        --afl->stage_max;

      }

    }

    *(u32 *)(out_buf + i) = orig;

  }                                               /* for i = 0; i < len - 3 */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_INTEREST32] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_INTEREST32] += afl->stage_max;

skip_interest:

  /********************
   * DICTIONARY STUFF *
   ********************/

  if (!afl->extras_cnt) { goto skip_user_extras; }

  /* Overwrite with user-supplied extras. */

  afl->stage_name = "user extras (over)";
  afl->stage_short = "ext_UO";
  afl->stage_cur = 0;
  afl->stage_max = afl->extras_cnt * len;

  afl->stage_val_type = STAGE_VAL_NONE;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < (u32)len; ++i) {

    u32 last_len = 0;

    afl->stage_cur_byte = i;

    /* Extras are sorted by size, from smallest to largest. This means
       that we don't have to worry about restoring the buffer in
       between writes at a particular offset determined by the outer
       loop. */

    for (j = 0; j < afl->extras_cnt; ++j) {

      /* Skip extras probabilistically if afl->extras_cnt > AFL_MAX_DET_EXTRAS.
         Also skip them if there's no room to insert the payload, if the token
         is redundant, or if its entire span has no bytes set in the effector
         map. */

      if ((afl->extras_cnt > afl->max_det_extras &&
           rand_below(afl, afl->extras_cnt) >= afl->max_det_extras) ||
          afl->extras[j].len > len - i ||
          !memcmp(afl->extras[j].data, out_buf + i, afl->extras[j].len) ||
          !memchr(eff_map + EFF_APOS(i), 1,
                  EFF_SPAN_ALEN(i, afl->extras[j].len))) {

        --afl->stage_max;
        continue;

      }

      last_len = afl->extras[j].len;
      memcpy(out_buf + i, afl->extras[j].data, last_len);

#ifdef INTROSPECTION
      snprintf(afl->mutation, sizeof(afl->mutation),
               "%s MOPT_EXTRAS_overwrite-%u-%u", afl->queue_cur->fname, i, j);
#endif

      if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

      ++afl->stage_cur;

    }

    /* Restore all the clobbered memory. */
    memcpy(out_buf + i, in_buf + i, last_len);

  }                                                   /* for i = 0; i < len */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_EXTRAS_UO] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_EXTRAS_UO] += afl->stage_max;

  /* Insertion of user-supplied extras. */

  afl->stage_name = "user extras (insert)";
  afl->stage_short = "ext_UI";
  afl->stage_cur = 0;
  afl->stage_max = afl->extras_cnt * (len + 1);

  orig_hit_cnt = new_hit_cnt;

  ex_tmp = afl_realloc(AFL_BUF_PARAM(ex), len + MAX_DICT_FILE);
  if (unlikely(!ex_tmp)) { PFATAL("alloc"); }

  for (i = 0; i <= (u32)len; ++i) {

    afl->stage_cur_byte = i;

    for (j = 0; j < afl->extras_cnt; ++j) {

      if (len + afl->extras[j].len > MAX_FILE) {

        --afl->stage_max;
        continue;

      }

      /* Insert token */
      memcpy(ex_tmp + i, afl->extras[j].data, afl->extras[j].len);

      /* Copy tail */
      memcpy(ex_tmp + i + afl->extras[j].len, out_buf + i, len - i);

#ifdef INTROSPECTION
      snprintf(afl->mutation, sizeof(afl->mutation),
               "%s MOPT_EXTRAS_insert-%u-%u", afl->queue_cur->fname, i, j);
#endif

      if (common_fuzz_stuff(afl, ex_tmp, len + afl->extras[j].len)) {

        goto abandon_entry;

      }

      ++afl->stage_cur;

    }

    /* Copy head */
    ex_tmp[i] = out_buf[i];

  }                                                  /* for i = 0; i <= len */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_EXTRAS_UI] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_EXTRAS_UI] += afl->stage_max;

skip_user_extras:

  if (!afl->a_extras_cnt) { goto skip_extras; }

  afl->stage_name = "auto extras (over)";
  afl->stage_short = "ext_AO";
  afl->stage_cur = 0;
  afl->stage_max = MIN(afl->a_extras_cnt, (u32)USE_AUTO_EXTRAS) * len;

  afl->stage_val_type = STAGE_VAL_NONE;

  orig_hit_cnt = new_hit_cnt;

  for (i = 0; i < (u32)len; ++i) {

    u32 last_len = 0;

    afl->stage_cur_byte = i;

    u32 min_extra_len = MIN(afl->a_extras_cnt, (u32)USE_AUTO_EXTRAS);
    for (j = 0; j < min_extra_len; ++j) {

      /* See the comment in the earlier code; extras are sorted by size. */

      if ((afl->a_extras[j].len) > (len - i) ||
          !memcmp(afl->a_extras[j].data, out_buf + i, afl->a_extras[j].len) ||
          !memchr(eff_map + EFF_APOS(i), 1,
                  EFF_SPAN_ALEN(i, afl->a_extras[j].len))) {

        --afl->stage_max;
        continue;

      }

      last_len = afl->a_extras[j].len;
      memcpy(out_buf + i, afl->a_extras[j].data, last_len);

#ifdef INTROSPECTION
      snprintf(afl->mutation, sizeof(afl->mutation),
               "%s MOPT_AUTO_EXTRAS_overwrite-%u-%u", afl->queue_cur->fname, i,
               j);
#endif

      if (common_fuzz_stuff(afl, out_buf, len)) { goto abandon_entry; }

      ++afl->stage_cur;

    }

    /* Restore all the clobbered memory. */
    memcpy(out_buf + i, in_buf + i, last_len);

  }                                                   /* for i = 0; i < len */

  new_hit_cnt = afl->queued_items + afl->saved_crashes;

  afl->stage_finds[STAGE_EXTRAS_AO] += new_hit_cnt - orig_hit_cnt;
  afl->stage_cycles[STAGE_EXTRAS_AO] += afl->stage_max;

skip_extras:

  /* If we made this to here without jumping to havoc_stage or abandon_entry,
     we're properly done with deterministic steps and can mark it as such
     in the .state/ directory. */

  if (!afl->queue_cur->passed_det) { mark_as_det_done(afl, afl->queue_cur); }

  /****************
   * RANDOM HAVOC *
   ****************/

havoc_stage:
pacemaker_fuzzing:

  afl->stage_cur_byte = -1;

  /* The havoc stage mutation code is also invoked when splicing files; if the
     splice_cycle variable is set, generate different descriptions and such. */

  if (!splice_cycle) {

    afl->stage_name = MOpt_globals.havoc_stagename;
    afl->stage_short = MOpt_globals.havoc_stagenameshort;
    afl->stage_max = (doing_det ? HAVOC_CYCLES_INIT : HAVOC_CYCLES) *
                     perf_score / afl->havoc_div / 100;

  } else {

    perf_score = orig_perf;

    snprintf(afl->stage_name_buf, STAGE_BUF_SIZE,
             MOpt_globals.splice_stageformat, splice_cycle);
    afl->stage_name = afl->stage_name_buf;
    afl->stage_short = MOpt_globals.splice_stagenameshort;
    afl->stage_max = SPLICE_HAVOC * perf_score / afl->havoc_div / 100;

  }

  s32 temp_len_puppet;

  // for (; afl->swarm_now < swarm_num; ++afl->swarm_now)
  {

    if (afl->key_puppet == 1) {

      if (unlikely(afl->orig_hit_cnt_puppet == 0)) {

        afl->orig_hit_cnt_puppet = afl->queued_items + afl->saved_crashes;
        afl->last_limit_time_start = get_cur_time();
        afl->SPLICE_CYCLES_puppet =
            (rand_below(
                 afl, SPLICE_CYCLES_puppet_up - SPLICE_CYCLES_puppet_low + 1) +
             SPLICE_CYCLES_puppet_low);

      }

    }                                            /* if afl->key_puppet == 1 */

    {

#ifndef IGNORE_FINDS
    havoc_stage_puppet:
#endif

      afl->stage_cur_byte = -1;

      /* The havoc stage mutation code is also invoked when splicing files; if
         the splice_cycle variable is set, generate different descriptions and
         such. */

      if (!splice_cycle) {

        afl->stage_name = MOpt_globals.havoc_stagename;
        afl->stage_short = MOpt_globals.havoc_stagenameshort;
        afl->stage_max = (doing_det ? HAVOC_CYCLES_INIT : HAVOC_CYCLES) *
                         perf_score / afl->havoc_div / 100;

      } else {

        perf_score = orig_perf;
        snprintf(afl->stage_name_buf, STAGE_BUF_SIZE,
                 MOpt_globals.splice_stageformat, splice_cycle);
        afl->stage_name = afl->stage_name_buf;
        afl->stage_short = MOpt_globals.splice_stagenameshort;
        afl->stage_max = SPLICE_HAVOC * perf_score / afl->havoc_div / 100;

      }

      if (afl->stage_max < HAVOC_MIN) { afl->stage_max = HAVOC_MIN; }

      temp_len = len;

      orig_hit_cnt = afl->queued_items + afl->saved_crashes;

      havoc_queued = afl->queued_items;

      u32 r_max;

      r_max = 15 + ((afl->extras_cnt + afl->a_extras_cnt) ? 2 : 0);

      if (unlikely(afl->expand_havoc && afl->ready_for_splicing_count > 1)) {

        /* add expensive havoc cases here, they are activated after a full
           cycle without finds happened */

        ++r_max;

      }

      for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max;
           ++afl->stage_cur) {

        u32 use_stacking = 1 << (1 + rand_below(afl, afl->havoc_stack_pow2));

        afl->stage_cur_val = use_stacking;

        for (i = 0; i < operator_num; ++i) {

          MOpt_globals.cycles_v3[i] = MOpt_globals.cycles_v2[i];

        }

#ifdef INTROSPECTION
        snprintf(afl->mutation, sizeof(afl->mutation), "%s MOPT_HAVOC-%u",
                 afl->queue_cur->fname, use_stacking);
#endif

        for (i = 0; i < use_stacking; ++i) {

          switch (select_algorithm(afl, r_max)) {

            case 0:
              /* Flip a single bit somewhere. Spooky! */
              FLIP_BIT(out_buf, rand_below(afl, temp_len << 3));
              MOpt_globals.cycles_v2[STAGE_FLIP1]++;
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " FLIP_BIT1");
              strcat(afl->mutation, afl->m_tmp);
#endif
              break;

            case 1:
              if (temp_len < 2) { break; }
              temp_len_puppet = rand_below(afl, (temp_len << 3) - 1);
              FLIP_BIT(out_buf, temp_len_puppet);
              FLIP_BIT(out_buf, temp_len_puppet + 1);
              MOpt_globals.cycles_v2[STAGE_FLIP2]++;
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " FLIP_BIT2");
              strcat(afl->mutation, afl->m_tmp);
#endif
              break;

            case 2:
              if (temp_len < 2) { break; }
              temp_len_puppet = rand_below(afl, (temp_len << 3) - 3);
              FLIP_BIT(out_buf, temp_len_puppet);
              FLIP_BIT(out_buf, temp_len_puppet + 1);
              FLIP_BIT(out_buf, temp_len_puppet + 2);
              FLIP_BIT(out_buf, temp_len_puppet + 3);
              MOpt_globals.cycles_v2[STAGE_FLIP4]++;
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " FLIP_BIT4");
              strcat(afl->mutation, afl->m_tmp);
#endif
              break;

            case 3:
              if (temp_len < 4) { break; }
              out_buf[rand_below(afl, temp_len)] ^= 0xFF;
              MOpt_globals.cycles_v2[STAGE_FLIP8]++;
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " FLIP_BIT8");
              strcat(afl->mutation, afl->m_tmp);
#endif
              break;

            case 4:
              if (temp_len < 8) { break; }
              *(u16 *)(out_buf + rand_below(afl, temp_len - 1)) ^= 0xFFFF;
              MOpt_globals.cycles_v2[STAGE_FLIP16]++;
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " FLIP_BIT16");
              strcat(afl->mutation, afl->m_tmp);
#endif
              break;

            case 5:
              if (temp_len < 8) { break; }
              *(u32 *)(out_buf + rand_below(afl, temp_len - 3)) ^= 0xFFFFFFFF;
              MOpt_globals.cycles_v2[STAGE_FLIP32]++;
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " FLIP_BIT32");
              strcat(afl->mutation, afl->m_tmp);
#endif
              break;

            case 6:
              out_buf[rand_below(afl, temp_len)] -=
                  1 + rand_below(afl, ARITH_MAX);
              out_buf[rand_below(afl, temp_len)] +=
                  1 + rand_below(afl, ARITH_MAX);
              MOpt_globals.cycles_v2[STAGE_ARITH8]++;
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH8");
              strcat(afl->mutation, afl->m_tmp);
#endif
              break;

            case 7:
              /* Randomly subtract from word, random endian. */
              if (temp_len < 8) { break; }
              if (rand_below(afl, 2)) {

                u32 pos = rand_below(afl, temp_len - 1);
                *(u16 *)(out_buf + pos) -= 1 + rand_below(afl, ARITH_MAX);
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH16-%u", pos);
                strcat(afl->mutation, afl->m_tmp);
#endif

              } else {

                u32 pos = rand_below(afl, temp_len - 1);
                u16 num = 1 + rand_below(afl, ARITH_MAX);
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH16BE-%u-%u",
                         pos, num);
                strcat(afl->mutation, afl->m_tmp);
#endif
                *(u16 *)(out_buf + pos) =
                    SWAP16(SWAP16(*(u16 *)(out_buf + pos)) - num);

              }

              /* Randomly add to word, random endian. */
              if (rand_below(afl, 2)) {

                u32 pos = rand_below(afl, temp_len - 1);
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH16+-%u", pos);
                strcat(afl->mutation, afl->m_tmp);
#endif
                *(u16 *)(out_buf + pos) += 1 + rand_below(afl, ARITH_MAX);

              } else {

                u32 pos = rand_below(afl, temp_len - 1);
                u16 num = 1 + rand_below(afl, ARITH_MAX);
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH16BE+-%u-%u",
                         pos, num);
                strcat(afl->mutation, afl->m_tmp);
#endif
                *(u16 *)(out_buf + pos) =
                    SWAP16(SWAP16(*(u16 *)(out_buf + pos)) + num);

              }

              MOpt_globals.cycles_v2[STAGE_ARITH16]++;
              break;

            case 8:
              /* Randomly subtract from dword, random endian. */
              if (temp_len < 8) { break; }
              if (rand_below(afl, 2)) {

                u32 pos = rand_below(afl, temp_len - 3);
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH32_-%u", pos);
                strcat(afl->mutation, afl->m_tmp);
#endif
                *(u32 *)(out_buf + pos) -= 1 + rand_below(afl, ARITH_MAX);

              } else {

                u32 pos = rand_below(afl, temp_len - 3);
                u32 num = 1 + rand_below(afl, ARITH_MAX);
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH32BE_-%u-%u",
                         pos, num);
                strcat(afl->mutation, afl->m_tmp);
#endif
                *(u32 *)(out_buf + pos) =
                    SWAP32(SWAP32(*(u32 *)(out_buf + pos)) - num);

              }

              /* Randomly add to dword, random endian. */
              // if (temp_len < 4) break;
              if (rand_below(afl, 2)) {

                u32 pos = rand_below(afl, temp_len - 3);
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH32+-%u", pos);
                strcat(afl->mutation, afl->m_tmp);
#endif
                *(u32 *)(out_buf + pos) += 1 + rand_below(afl, ARITH_MAX);

              } else {

                u32 pos = rand_below(afl, temp_len - 3);
                u32 num = 1 + rand_below(afl, ARITH_MAX);
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " ARITH32BE+-%u-%u",
                         pos, num);
                strcat(afl->mutation, afl->m_tmp);
#endif
                *(u32 *)(out_buf + pos) =
                    SWAP32(SWAP32(*(u32 *)(out_buf + pos)) + num);

              }

              MOpt_globals.cycles_v2[STAGE_ARITH32]++;
              break;

            case 9:
              /* Set byte to interesting value. */
              if (temp_len < 4) { break; }
              out_buf[rand_below(afl, temp_len)] =
                  interesting_8[rand_below(afl, sizeof(interesting_8))];
              MOpt_globals.cycles_v2[STAGE_INTEREST8]++;
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " INTERESTING8");
              strcat(afl->mutation, afl->m_tmp);
#endif
              break;

            case 10:
              /* Set word to interesting value, randomly choosing endian. */
              if (temp_len < 8) { break; }
              if (rand_below(afl, 2)) {

#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " INTERESTING16");
                strcat(afl->mutation, afl->m_tmp);
#endif
                *(u16 *)(out_buf + rand_below(afl, temp_len - 1)) =
                    interesting_16[rand_below(afl,
                                              sizeof(interesting_16) >> 1)];

              } else {

#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " INTERESTING16BE");
                strcat(afl->mutation, afl->m_tmp);
#endif
                *(u16 *)(out_buf + rand_below(afl, temp_len - 1)) =
                    SWAP16(interesting_16[rand_below(
                        afl, sizeof(interesting_16) >> 1)]);

              }

              MOpt_globals.cycles_v2[STAGE_INTEREST16]++;
              break;

            case 11:
              /* Set dword to interesting value, randomly choosing endian. */

              if (temp_len < 8) { break; }

              if (rand_below(afl, 2)) {

#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " INTERESTING32");
                strcat(afl->mutation, afl->m_tmp);
#endif
                *(u32 *)(out_buf + rand_below(afl, temp_len - 3)) =
                    interesting_32[rand_below(afl,
                                              sizeof(interesting_32) >> 2)];

              } else {

#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " INTERESTING32BE");
                strcat(afl->mutation, afl->m_tmp);
#endif
                *(u32 *)(out_buf + rand_below(afl, temp_len - 3)) =
                    SWAP32(interesting_32[rand_below(
                        afl, sizeof(interesting_32) >> 2)]);

              }

              MOpt_globals.cycles_v2[STAGE_INTEREST32]++;
              break;

            case 12:

              /* Just set a random byte to a random value. Because,
                 why not. We use XOR with 1-255 to eliminate the
                 possibility of a no-op. */

              out_buf[rand_below(afl, temp_len)] ^= 1 + rand_below(afl, 255);
              MOpt_globals.cycles_v2[STAGE_RANDOMBYTE]++;
#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " RAND8");
              strcat(afl->mutation, afl->m_tmp);
#endif
              break;

            case 13: {

              /* Delete bytes. We're making this a bit more likely
                 than insertion (the next option) in hopes of keeping
                 files reasonably small. */

              u32 del_from, del_len;

              if (temp_len < 2) { break; }

              /* Don't delete too much. */

              del_len = choose_block_len(afl, temp_len - 1);

              del_from = rand_below(afl, temp_len - del_len + 1);

#ifdef INTROSPECTION
              snprintf(afl->m_tmp, sizeof(afl->m_tmp), " DEL-%u%u", del_from,
                       del_len);
              strcat(afl->mutation, afl->m_tmp);
#endif
              memmove(out_buf + del_from, out_buf + del_from + del_len,
                      temp_len - del_from - del_len);

              temp_len -= del_len;
              MOpt_globals.cycles_v2[STAGE_DELETEBYTE]++;
              break;

            }

            case 14:

              if (temp_len + HAVOC_BLK_XL < MAX_FILE) {

                /* Clone bytes (75%) or insert a block of constant bytes (25%).
                 */

                u8  actually_clone = rand_below(afl, 4);
                u32 clone_from, clone_to, clone_len;
                u8 *new_buf;

                if (likely(actually_clone)) {

                  clone_len = choose_block_len(afl, temp_len);
                  clone_from = rand_below(afl, temp_len - clone_len + 1);

                } else {

                  clone_len = choose_block_len(afl, HAVOC_BLK_XL);
                  clone_from = 0;

                }

                clone_to = rand_below(afl, temp_len);

#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " CLONE_%s-%u-%u-%u",
                         actually_clone ? "clone" : "insert", clone_from,
                         clone_to, clone_len);
                strcat(afl->mutation, afl->m_tmp);
#endif
                new_buf = afl_realloc(AFL_BUF_PARAM(out_scratch),
                                      temp_len + clone_len);
                if (unlikely(!new_buf)) { PFATAL("alloc"); }

                /* Head */

                memcpy(new_buf, out_buf, clone_to);

                /* Inserted part */

                if (actually_clone) {

                  memcpy(new_buf + clone_to, out_buf + clone_from, clone_len);

                } else {

                  memset(new_buf + clone_to,
                         rand_below(afl, 2)
                             ? rand_below(afl, 256)
                             : out_buf[rand_below(afl, temp_len)],
                         clone_len);

                }

                /* Tail */
                memcpy(new_buf + clone_to + clone_len, out_buf + clone_to,
                       temp_len - clone_to);

                out_buf = new_buf;
                afl_swap_bufs(AFL_BUF_PARAM(out), AFL_BUF_PARAM(out_scratch));
                temp_len += clone_len;
                MOpt_globals.cycles_v2[STAGE_Clone75]++;

              }

              break;

            case 15: {

              /* Overwrite bytes with a randomly selected chunk (75%) or fixed
                 bytes (25%). */

              u32 copy_from, copy_to, copy_len;

              if (temp_len < 2) { break; }

              copy_len = choose_block_len(afl, temp_len - 1);

              copy_from = rand_below(afl, temp_len - copy_len + 1);
              copy_to = rand_below(afl, temp_len - copy_len + 1);

              if (likely(rand_below(afl, 4))) {

                if (likely(copy_from != copy_to)) {

#ifdef INTROSPECTION
                  snprintf(afl->m_tmp, sizeof(afl->m_tmp),
                           " OVERWRITE_COPY-%u-%u-%u", copy_from, copy_to,
                           copy_len);
                  strcat(afl->mutation, afl->m_tmp);
#endif
                  memmove(out_buf + copy_to, out_buf + copy_from, copy_len);

                }

              } else {

#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp),
                         " OVERWRITE_FIXED-%u-%u-%u", copy_from, copy_to,
                         copy_len);
                strcat(afl->mutation, afl->m_tmp);
#endif
                memset(out_buf + copy_to,
                       rand_below(afl, 2) ? rand_below(afl, 256)
                                          : out_buf[rand_below(afl, temp_len)],
                       copy_len);

              }

              MOpt_globals.cycles_v2[STAGE_OverWrite75]++;
              break;

            }                                                    /* case 15 */

              /* Values 16 and 17 can be selected only if there are any extras
                 present in the dictionaries. */

            case 16: {

              /* Overwrite bytes with an extra. */

              if (!afl->extras_cnt ||
                  (afl->a_extras_cnt && rand_below(afl, 2))) {

                /* No user-specified extras or odds in our favor. Let's use an
                  auto-detected one. */

                u32 use_extra = rand_below(afl, afl->a_extras_cnt);
                u32 extra_len = afl->a_extras[use_extra].len;

                if (extra_len > (u32)temp_len) break;

                u32 insert_at = rand_below(afl, temp_len - extra_len + 1);
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp),
                         " AUTO_EXTRA_OVERWRITE-%u-%u", insert_at, extra_len);
                strcat(afl->mutation, afl->m_tmp);
#endif
                memcpy(out_buf + insert_at, afl->a_extras[use_extra].data,
                       extra_len);

              } else {

                /* No auto extras or odds in our favor. Use the dictionary. */

                u32 use_extra = rand_below(afl, afl->extras_cnt);
                u32 extra_len = afl->extras[use_extra].len;

                if (extra_len > (u32)temp_len) break;

                u32 insert_at = rand_below(afl, temp_len - extra_len + 1);
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp),
                         " EXTRA_OVERWRITE-%u-%u", insert_at, extra_len);
                strcat(afl->mutation, afl->m_tmp);
#endif
                memcpy(out_buf + insert_at, afl->extras[use_extra].data,
                       extra_len);

              }

              MOpt_globals.cycles_v2[STAGE_OverWriteExtra]++;

              break;

            }

              /* Insert an extra. */

            case 17: {

              u32 use_extra, extra_len,
                  insert_at = rand_below(afl, temp_len + 1);
              u8 *ptr;

              /* Insert an extra. Do the same dice-rolling stuff as for the
                previous case. */

              if (!afl->extras_cnt ||
                  (afl->a_extras_cnt && rand_below(afl, 2))) {

                use_extra = rand_below(afl, afl->a_extras_cnt);
                extra_len = afl->a_extras[use_extra].len;
                ptr = afl->a_extras[use_extra].data;
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp),
                         " AUTO_EXTRA_INSERT-%u-%u", insert_at, extra_len);
                strcat(afl->mutation, afl->m_tmp);
#endif

              } else {

                use_extra = rand_below(afl, afl->extras_cnt);
                extra_len = afl->extras[use_extra].len;
                ptr = afl->extras[use_extra].data;
#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp), " EXTRA_INSERT-%u-%u",
                         insert_at, extra_len);
                strcat(afl->mutation, afl->m_tmp);
#endif

              }

              if (temp_len + extra_len >= MAX_FILE) break;

              out_buf = afl_realloc(AFL_BUF_PARAM(out), temp_len + extra_len);
              if (unlikely(!out_buf)) { PFATAL("alloc"); }

              /* Tail */
              memmove(out_buf + insert_at + extra_len, out_buf + insert_at,
                      temp_len - insert_at);

              /* Inserted part */
              memcpy(out_buf + insert_at, ptr, extra_len);

              temp_len += extra_len;
              MOpt_globals.cycles_v2[STAGE_InsertExtra]++;
              break;

            }

            default: {

              if (unlikely(afl->ready_for_splicing_count < 2)) break;

              u32 tid;
              do {

                tid = rand_below(afl, afl->queued_items);

              } while (tid == afl->current_entry ||

                       afl->queue_buf[tid]->len < 4);

              /* Get the testcase for splicing. */
              struct queue_entry *target = afl->queue_buf[tid];
              u32                 new_len = target->len;
              u8 *                new_buf = queue_testcase_get(afl, target);

              if ((temp_len >= 2 && rand_below(afl, 2)) ||
                  temp_len + HAVOC_BLK_XL >= MAX_FILE) {

                /* overwrite mode */

                u32 copy_from, copy_to, copy_len;

                copy_len = choose_block_len(afl, new_len - 1);
                if (copy_len > temp_len) copy_len = temp_len;

                copy_from = rand_below(afl, new_len - copy_len + 1);
                copy_to = rand_below(afl, temp_len - copy_len + 1);

#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp),
                         " SPLICE_OVERWRITE-%u-%u-%u-%s", copy_from, copy_to,
                         copy_len, target->fname);
                strcat(afl->mutation, afl->m_tmp);
#endif
                memmove(out_buf + copy_to, new_buf + copy_from, copy_len);

              } else {

                /* insert mode */

                u32 clone_from, clone_to, clone_len;

                clone_len = choose_block_len(afl, new_len);
                clone_from = rand_below(afl, new_len - clone_len + 1);
                clone_to = rand_below(afl, temp_len + 1);

                u8 *temp_buf = afl_realloc(AFL_BUF_PARAM(out_scratch),
                                           temp_len + clone_len + 1);
                if (unlikely(!temp_buf)) { PFATAL("alloc"); }

#ifdef INTROSPECTION
                snprintf(afl->m_tmp, sizeof(afl->m_tmp),
                         " SPLICE_INSERT-%u-%u-%u-%s", clone_from, clone_to,
                         clone_len, target->fname);
                strcat(afl->mutation, afl->m_tmp);
#endif
                /* Head */

                memcpy(temp_buf, out_buf, clone_to);

                /* Inserted part */

                memcpy(temp_buf + clone_to, new_buf + clone_from, clone_len);

                /* Tail */
                memcpy(temp_buf + clone_to + clone_len, out_buf + clone_to,
                       temp_len - clone_to);

                out_buf = temp_buf;
                afl_swap_bufs(AFL_BUF_PARAM(out), AFL_BUF_PARAM(out_scratch));
                temp_len += clone_len;

              }

              MOpt_globals.cycles_v2[STAGE_Splice]++;
              break;

            }  // end of default:

          }                                    /* switch select_algorithm() */

        }                                      /* for i=0; i < use_stacking */

        ++*MOpt_globals.pTime;

        u64 temp_total_found = afl->queued_items + afl->saved_crashes;

        if (common_fuzz_stuff(afl, out_buf, temp_len)) {

          goto abandon_entry_puppet;

        }

        /* out_buf might have been mangled a bit, so let's restore it to its
           original size and shape. */

        out_buf = afl_realloc(AFL_BUF_PARAM(out), len);
        if (unlikely(!out_buf)) { PFATAL("alloc"); }
        temp_len = len;
        memcpy(out_buf, in_buf, len);

        /* If we're finding new stuff, let's run for a bit longer, limits
           permitting. */

        if (afl->queued_items != havoc_queued) {

          if (perf_score <= afl->havoc_max_mult * 100) {

            afl->stage_max *= 2;
            perf_score *= 2;

          }

          havoc_queued = afl->queued_items;

        }

        if (unlikely(afl->queued_items + afl->saved_crashes >
                     temp_total_found)) {

          u64 temp_temp_puppet =
              afl->queued_items + afl->saved_crashes - temp_total_found;
          afl->total_puppet_find = afl->total_puppet_find + temp_temp_puppet;

          if (MOpt_globals.is_pilot_mode) {

            for (i = 0; i < operator_num; ++i) {

              if (MOpt_globals.cycles_v2[i] > MOpt_globals.cycles_v3[i]) {

                MOpt_globals.finds_v2[i] += temp_temp_puppet;

              }

            }

          } else {

            for (i = 0; i < operator_num; i++) {

              if (afl->core_operator_cycles_puppet_v2[i] >
                  afl->core_operator_cycles_puppet_v3[i])

                afl->core_operator_finds_puppet_v2[i] += temp_temp_puppet;

            }

          }

        }                                                             /* if */

      } /* for (afl->stage_cur = 0; afl->stage_cur < afl->stage_max;

           ++afl->stage_cur) { */

      new_hit_cnt = afl->queued_items + afl->saved_crashes;

      if (MOpt_globals.is_pilot_mode) {

        if (!splice_cycle) {

          afl->stage_finds[STAGE_HAVOC] += new_hit_cnt - orig_hit_cnt;
          afl->stage_cycles[STAGE_HAVOC] += afl->stage_max;

        } else {

          afl->stage_finds[STAGE_SPLICE] += new_hit_cnt - orig_hit_cnt;
          afl->stage_cycles[STAGE_SPLICE] += afl->stage_max;

        }

      }

#ifndef IGNORE_FINDS

      /************
       * SPLICING *
       ************/

    retry_splicing_puppet:

      if (afl->use_splicing &&
          splice_cycle++ < (u32)afl->SPLICE_CYCLES_puppet &&
          afl->ready_for_splicing_count > 1 && afl->queue_cur->len >= 4) {

        struct queue_entry *target;
        u32                 tid, split_at;
        u8 *                new_buf;
        s32                 f_diff, l_diff;

        /* First of all, if we've modified in_buf for havoc, let's clean that
           up... */

        if (in_buf != orig_in) {

          in_buf = orig_in;
          len = afl->queue_cur->len;

        }

        /* Pick a random queue entry and seek to it. Don't splice with yourself.
         */

        do {

          tid = rand_below(afl, afl->queued_items);

        } while (tid == afl->current_entry || afl->queue_buf[tid]->len < 4);

        afl->splicing_with = tid;
        target = afl->queue_buf[tid];

        /* Read the testcase into a new buffer. */
        new_buf = queue_testcase_get(afl, target);

        /* Find a suitable splicin g location, somewhere between the first and
           the last differing byte. Bail out if the difference is just a single
           byte or so. */

        locate_diffs(in_buf, new_buf, MIN(len, target->len), &f_diff, &l_diff);

        if (f_diff < 0 || l_diff < 2 || f_diff == l_diff) {

          goto retry_splicing_puppet;

        }

        /* Split somewhere between the first and last differing byte. */

        split_at = f_diff + rand_below(afl, l_diff - f_diff);

        /* Do the thing. */

        len = target->len;
        afl->in_scratch_buf = afl_realloc(AFL_BUF_PARAM(in_scratch), len);
        memcpy(afl->in_scratch_buf, in_buf, split_at);
        memcpy(afl->in_scratch_buf + split_at, new_buf, len - split_at);
        in_buf = afl->in_scratch_buf;
        afl_swap_bufs(AFL_BUF_PARAM(in), AFL_BUF_PARAM(in_scratch));

        out_buf = afl_realloc(AFL_BUF_PARAM(out), len);
        if (unlikely(!out_buf)) { PFATAL("alloc"); }
        memcpy(out_buf, in_buf, len);

        goto havoc_stage_puppet;

      }                                                  /* if splice_cycle */

#endif                                                     /* !IGNORE_FINDS */

      ret_val = 0;

    abandon_entry:
    abandon_entry_puppet:

      if ((s64)splice_cycle >= afl->SPLICE_CYCLES_puppet) {

        afl->SPLICE_CYCLES_puppet =
            (rand_below(
                 afl, SPLICE_CYCLES_puppet_up - SPLICE_CYCLES_puppet_low + 1) +
             SPLICE_CYCLES_puppet_low);

      }

      afl->splicing_with = -1;

      /* Update afl->pending_not_fuzzed count if we made it through the
         calibration cycle and have not seen this entry before. */
      /*
        // TODO FIXME: I think we need this plus need an -L -1 check
        if (!afl->stop_soon && !afl->queue_cur->cal_failed &&
            (afl->queue_cur->was_fuzzed == 0 || afl->queue_cur->fuzz_level == 0)
        && !afl->queue_cur->disabled) {

          if (!afl->queue_cur->was_fuzzed) {

            --afl->pending_not_fuzzed;
            afl->queue_cur->was_fuzzed = 1;
            if (afl->queue_cur->favored) { --afl->pending_favored; }

          }

        }

      */

      orig_in = NULL;

      if (afl->key_puppet == 1) {

        if (unlikely(
                afl->queued_items + afl->saved_crashes >
                ((afl->queued_items + afl->saved_crashes) * limit_time_bound +
                 afl->orig_hit_cnt_puppet))) {

          afl->key_puppet = 0;
          afl->orig_hit_cnt_puppet = 0;
          afl->last_limit_time_start = 0;

        }

      }

      if (unlikely(*MOpt_globals.pTime > MOpt_globals.period)) {

        afl->total_pacemaker_time += *MOpt_globals.pTime;
        *MOpt_globals.pTime = 0;
        new_hit_cnt = afl->queued_items + afl->saved_crashes;

        if (MOpt_globals.is_pilot_mode) {

          afl->swarm_fitness[afl->swarm_now] =
              (double)(afl->total_puppet_find - afl->temp_puppet_find) /
              ((double)(afl->tmp_pilot_time) / afl->period_pilot_tmp);

        }

        afl->temp_puppet_find = afl->total_puppet_find;
        for (i = 0; i < operator_num; ++i) {

          if (MOpt_globals.is_pilot_mode) {

            double temp_eff = 0.0;

            if (MOpt_globals.cycles_v2[i] > MOpt_globals.cycles[i]) {

              temp_eff =
                  (double)(MOpt_globals.finds_v2[i] - MOpt_globals.finds[i]) /
                  (double)(MOpt_globals.cycles_v2[i] - MOpt_globals.cycles[i]);

            }

            if (afl->eff_best[afl->swarm_now][i] < temp_eff) {

              afl->eff_best[afl->swarm_now][i] = temp_eff;
              afl->L_best[afl->swarm_now][i] = afl->x_now[afl->swarm_now][i];

            }

          }

          MOpt_globals.finds[i] = MOpt_globals.finds_v2[i];
          MOpt_globals.cycles[i] = MOpt_globals.cycles_v2[i];

        }                                    /* for i = 0; i < operator_num */

        if (MOpt_globals.is_pilot_mode) {

          afl->swarm_now = afl->swarm_now + 1;
          if (afl->swarm_now == swarm_num) {

            afl->key_module = 1;
            for (i = 0; i < operator_num; ++i) {

              afl->core_operator_cycles_puppet_v2[i] =
                  afl->core_operator_cycles_puppet[i];
              afl->core_operator_cycles_puppet_v3[i] =
                  afl->core_operator_cycles_puppet[i];
              afl->core_operator_finds_puppet_v2[i] =
                  afl->core_operator_finds_puppet[i];

            }

            double swarm_eff = 0.0;
            afl->swarm_now = 0;
            for (i = 0; i < swarm_num; ++i) {

              if (afl->swarm_fitness[i] > swarm_eff) {

                swarm_eff = afl->swarm_fitness[i];
                afl->swarm_now = i;

              }

            }

            if (afl->swarm_now < 0 || afl->swarm_now > swarm_num - 1) {

              PFATAL("swarm_now error number  %d", afl->swarm_now);

            }

          }                               /* if afl->swarm_now == swarm_num */

          /* adjust pointers dependent on 'afl->swarm_now' */
          afl->mopt_globals_pilot.finds =
              afl->stage_finds_puppet[afl->swarm_now];
          afl->mopt_globals_pilot.finds_v2 =
              afl->stage_finds_puppet_v2[afl->swarm_now];
          afl->mopt_globals_pilot.cycles =
              afl->stage_cycles_puppet[afl->swarm_now];
          afl->mopt_globals_pilot.cycles_v2 =
              afl->stage_cycles_puppet_v2[afl->swarm_now];
          afl->mopt_globals_pilot.cycles_v3 =
              afl->stage_cycles_puppet_v3[afl->swarm_now];

        } else {

          for (i = 0; i < operator_num; i++) {

            afl->core_operator_finds_puppet[i] =
                afl->core_operator_finds_puppet_v2[i];
            afl->core_operator_cycles_puppet[i] =
                afl->core_operator_cycles_puppet_v2[i];

          }

          afl->key_module = 2;

          afl->old_hit_count = new_hit_cnt;

        }                                                  /* if pilot_mode */

      }         /* if (unlikely(*MOpt_globals.pTime > MOpt_globals.period)) */

    }                                                              /* block */

  }                                                                /* block */

  return ret_val;

}

#undef FLIP_BIT

u8 core_fuzzing(afl_state_t *afl) {

  return mopt_common_fuzzing(afl, afl->mopt_globals_core);

}

u8 pilot_fuzzing(afl_state_t *afl) {

  return mopt_common_fuzzing(afl, afl->mopt_globals_pilot);

}

void pso_updating(afl_state_t *afl) {

  afl->g_now++;
  if (afl->g_now > afl->g_max) { afl->g_now = 0; }
  afl->w_now =
      (afl->w_init - afl->w_end) * (afl->g_max - afl->g_now) / (afl->g_max) +
      afl->w_end;
  int tmp_swarm, i, j;
  u64 temp_operator_finds_puppet = 0;
  for (i = 0; i < operator_num; ++i) {

    afl->operator_finds_puppet[i] = afl->core_operator_finds_puppet[i];

    for (j = 0; j < swarm_num; ++j) {

      afl->operator_finds_puppet[i] =
          afl->operator_finds_puppet[i] + afl->stage_finds_puppet[j][i];

    }

    temp_operator_finds_puppet =
        temp_operator_finds_puppet + afl->operator_finds_puppet[i];

  }

  for (i = 0; i < operator_num; ++i) {

    if (afl->operator_finds_puppet[i]) {

      afl->G_best[i] = (double)((double)(afl->operator_finds_puppet[i]) /
                                (double)(temp_operator_finds_puppet));

    }

  }

  for (tmp_swarm = 0; tmp_swarm < swarm_num; ++tmp_swarm) {

    double x_temp = 0.0;
    for (i = 0; i < operator_num; ++i) {

      afl->probability_now[tmp_swarm][i] = 0.0;
      afl->v_now[tmp_swarm][i] =
          afl->w_now * afl->v_now[tmp_swarm][i] +
          RAND_C * (afl->L_best[tmp_swarm][i] - afl->x_now[tmp_swarm][i]) +
          RAND_C * (afl->G_best[i] - afl->x_now[tmp_swarm][i]);
      afl->x_now[tmp_swarm][i] += afl->v_now[tmp_swarm][i];
      if (afl->x_now[tmp_swarm][i] > v_max) {

        afl->x_now[tmp_swarm][i] = v_max;

      } else if (afl->x_now[tmp_swarm][i] < v_min) {

        afl->x_now[tmp_swarm][i] = v_min;

      }

      x_temp += afl->x_now[tmp_swarm][i];

    }

    for (i = 0; i < operator_num; ++i) {

      afl->x_now[tmp_swarm][i] = afl->x_now[tmp_swarm][i] / x_temp;
      if (likely(i != 0)) {

        afl->probability_now[tmp_swarm][i] =
            afl->probability_now[tmp_swarm][i - 1] + afl->x_now[tmp_swarm][i];

      } else {

        afl->probability_now[tmp_swarm][i] = afl->x_now[tmp_swarm][i];

      }

    }

    if (afl->probability_now[tmp_swarm][operator_num - 1] < 0.99 ||
        afl->probability_now[tmp_swarm][operator_num - 1] > 1.01) {

      FATAL("ERROR probability");

    }

  }

  afl->swarm_now = 0;
  afl->key_module = 0;

}

/* larger change for MOpt implementation: the original fuzz_one was renamed
   to fuzz_one_original. All documentation references to fuzz_one therefore
   mean fuzz_one_original */

u8 fuzz_one(afl_state_t *afl) {

  int key_val_lv_1 = 0, key_val_lv_2 = 0;

#ifdef _AFL_DOCUMENT_MUTATIONS

  u8 path_buf[PATH_MAX];
  if (afl->do_document == 0) {

    snprintf(path_buf, PATH_MAX, "%s/mutations", afl->out_dir);
    afl->do_document = mkdir(path_buf, 0700);  // if it exists we do not care
    afl->do_document = 1;

  } else {

    afl->do_document = 2;
    afl->stop_soon = 2;

  }

#endif

  // if limit_time_sig == -1 then both are run after each other

  if (afl->limit_time_sig <= 0) { key_val_lv_1 = fuzz_one_original(afl); }

  if (afl->limit_time_sig != 0) {

    if (afl->key_module == 0) {

      key_val_lv_2 = pilot_fuzzing(afl);

    } else if (afl->key_module == 1) {

      key_val_lv_2 = core_fuzzing(afl);

    } else if (afl->key_module == 2) {

      pso_updating(afl);

    }

  }

  return (key_val_lv_1 | key_val_lv_2);

}

