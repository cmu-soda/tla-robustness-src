#!/bin/sh

max_time="10m"

script_path=$(dirname "${BASH_SOURCE[0]}")
loc=$(readlink -f "${script_path}")
tlc="${loc}/../bin/tla2tools.jar"

dirs=("tla/consensus_epr/4-4"
    "tla/mldr/2")

names=("consensus_epr"
    "MongoLoglessDynamicRaft")

benches=("pyv-consensus-epr-4-4"
    "mldr-2")

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
