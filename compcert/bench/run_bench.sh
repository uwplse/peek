#!/bin/bash
set -e

sec=run_`date +%y%m%d%H%M%S`

outfile=ccb_run_results.csv

#start in verso/compcert/bench
mkdir bench_results/$sec;
cd ..; # go to verso/compcert

echo '[run_bench] Pulling...'

git pull;

echo '[run_bench] Building...'

make -j8;
cd test/c; # go to verso/compcert/test/c

make all;
make all_nopeep;
make all_handtuned;
# make all_gcc;
# make all_gcc_nopeep;
# make all_clang;

#run each benchmark 7 times
echo '[run_bench] Running...'
for i in `seq 0 6`;
do
    echo '[run_bench] Run #'$i
    make bench > ../../bench/bench_results/$sec/bench_results_$i.txt 2>&1;
    make bench_nopeep > ../../bench/bench_results/$sec/bench_results_nopeep_$i.txt 2>&1;
    make bench_handtuned > ../../bench/bench_results/$sec/bench_results_handtuned_$i.txt 2>&1;
    # make bench_gcc > ../../bench/bench_results/$sec/bench_results_gcc_$i.txt 2>&1;
    # make bench_clang > ../../bench/bench_results/$sec/bench_results_clang_$i.txt 2>&1;
done

cp *.s ../../bench/bench_results/$sec/
cd ../../bench/bench_results/$sec #go into results folder


#collect all results into one file
echo '[run_bench] Parsing...'
for i in `seq 0 6`;
do
    python ../../parse_results.py bench_results_$i.txt >> peek.txt
    python ../../parse_results.py bench_results_nopeep_$i.txt >> nopeek.txt
    python ../../parse_results.py bench_results_handtuned_$i.txt >> handtuned.txt
    # python ../../parse_results.py bench_results_gcc_$i.txt >> gcc.txt
    # python ../../parse_results.py bench_results_clang_$i.txt >> clang.txt
done


#make file into one thing
python ../../collect_results.py peek.txt nopeek.txt handtuned.txt > $outfile #gcc.txt clang.txt

cd ../../../peeps

#extract peephole definitions

./extract_peep_defs.sh
cp peep_defs.txt ../bench/bench_results/$sec/

cd ../bench/bench_results #go up to bench_results folder

cp -r $sec ~/verso-papers/dash/evaluation/

cd ~/verso-papers/dash/

git pull;

echo '[run_bench] Publishing...'
make

echo '[run_bench] Done!'

