#!/bin/sh

time ./run_tlc.sh | tee out/tlc_output.log
time ./run_custom.sh | tee out/cust_output.log
time ./run_heuristic.sh | tee out/heur_output.log
time ./run_naive.sh | tee out/naive_output.log
