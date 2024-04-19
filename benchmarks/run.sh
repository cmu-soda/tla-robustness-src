flag="${1}"

max_time="10m"

script_path=$(dirname "${BASH_SOURCE[0]}")
loc=$(readlink -f "${script_path}")
recomp_verify="${loc}/../recomp-verify.py"

source benchmark_defs.sh

for i in "${!dirs[@]}"
do
    d=${dirs[i]}
    n=${names[i]}
    bench=${benches[i]}

    pushd "$d" >> /dev/null
    echo "Benchmark ${i}: ${bench}" 
    if [[ "${flag}" = "" ]]
    then
        /usr/bin/time -h -o time.txt timeout --foreground -s KILL "${max_time}" python3 "${recomp_verify}" "${n}.tla" "${n}.cfg"
    else
        /usr/bin/time -h -o time.txt timeout --foreground -s KILL "${max_time}" python3 "${recomp_verify}" "${n}.tla" "${n}.cfg" "${flag}"
    fi

    # kill any zombine processes
    ps x | grep recomp-verify | grep -v grep | awk '{print $1}' | xargs kill -9
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
