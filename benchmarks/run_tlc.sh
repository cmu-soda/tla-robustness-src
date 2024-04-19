#!/bin/sh

max_time="10m"

script_path=$(dirname "${BASH_SOURCE[0]}")
loc=$(readlink -f "${script_path}")
tlc="${loc}/../bin/tla2tools.jar"

source benchmark_defs.sh

for i in "${!dirs[@]}"
do
    d=${dirs[i]}
    n=${names[i]}
    bench=${benches[i]}

    pushd "$d" >> /dev/null
    echo "Benchmark ${i}: ${bench}" 

    /usr/bin/time -h -o time.txt timeout --foreground -s KILL "${max_time}" java -jar "${tlc}" -deadlock "${n}.tla"
    sleep 1

    wall="NA"
    if [[ -f time.txt ]]
    then
        wall=$(cat time.txt | sed 's/real.*$//g' | tr -d ' \t\r')
    fi
    rm -f time.txt
    echo "Run time: ${wall}"
    echo
    popd >> /dev/null
done
