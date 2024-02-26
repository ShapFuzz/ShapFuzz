#!/usr/bin/env python
# -*- coding: utf-8 -*-


# using example: python ./truzz_neuzz/nn.py --program ./programs/readelf/readelf --before -a --after --seeds ./programs/readelf/neuzz_in/

import os
import sys
import glob
import math
import time
import random
import subprocess
import numpy as np
from collections import Counter
from sklearn.cluster import KMeans,MiniBatchKMeans
from sklearn.metrics import pairwise_distances_argmin_min
from sklearn.decomposition import PCA


HOST = '127.0.0.1'
PORT = 13000


# process training data from afl raw data
def process_data(args):

    program = args['program']
    seeds_path = args['seeds']
    if 'before' in args.keys():
        before = args['before']
    if 'after' in args.keys():
        after = args['after']

    seed_list = glob.glob(seeds_path + '/*')

    print(seeds_path)
    print(before)
    print(after)

    call = subprocess.check_output

    # obtain raw bitmaps
    raw_bitmap = {}
    tmp_cnt = []
    out = ''
    for f in seed_list:
        print(f)
        tmp_list = []
        try:
            # print(['./afl-showmap', '-q', '-e', '-o', '/dev/stdout', '-m', '512', '-t', '500'] + [program, before, f, after])
            out = call(['./afl-showmap', '-q', '-e', '-o', '/dev/stdout', '-m', '512', '-t', '500'] + [program, before, f, after])
        except subprocess.CalledProcessError:
            print("find a crash")
        for line in out.splitlines():
            edge = line.split(b':')[0]
            tmp_cnt.append(edge)
            tmp_list.append(edge)
        print(len(tmp_list))
        raw_bitmap[f] = tmp_list
    counter = Counter(tmp_cnt).most_common()

    # save bitmaps to individual numpy label
    label = [int(f[0]) for f in counter]
    bitmap = np.zeros((len(seed_list), len(label)))
    for idx, i in enumerate(seed_list):
        tmp = raw_bitmap[i]
        for j in tmp:
            if int(j) in label:
                bitmap[idx][label.index((int(j)))] = 1

    # label dimension reduction
    fit_bitmap = np.unique(bitmap, axis=1)
    print("data dimension" + str(fit_bitmap.shape))
    print(len(seed_list))
    # start = time.clock()
    kmeans = MiniBatchKMeans(n_clusters=10, random_state=0, batch_size=64).fit(fit_bitmap)
    print(kmeans.cluster_centers_)
    closest, _ = pairwise_distances_argmin_min(kmeans.cluster_centers_, fit_bitmap)
    print(closest)
    
    # end= time.clock()
    # print('Running time: %s Seconds'%(end-start))

    # check
    # for i in range(len(closest)):
    #     print((kmeans.cluster_centers_)[i])
    #     print(fit_bitmap[closest[i]])

    if os.path.exists(args['path']):
        os.remove(args['path'])
    f = open(args['path'], "a")
    # write the result
    for i in closest:
        seed_name = seed_list[i]
        print(seed_name)
        if i == closest[-1]:
            f.write(seed_name)
        else:
            f.write(seed_name + "\n")
    f.close()


if __name__ == '__main__':
    argvv = sys.argv[1:]

    args = {}
    args['program'] = " ".join([argvv[argvv.index("--program") + 1]])
    args['showmap'] = " ".join([argvv[argvv.index("--showmap") + 1]])
    args['path'] = " ".join([argvv[argvv.index("--path") + 1]])
    args['before'] = " ".join(argvv[argvv.index("--before") + 1:argvv.index("--after")])
    args['after'] = " ".join(argvv[argvv.index("--after") + 1:argvv.index("--seeds")])
    args['seeds'] = " ".join([argvv[argvv.index("--seeds") + 1]])
    print(args)

    process_data(args)
