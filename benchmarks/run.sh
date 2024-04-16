flag="${1}"

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
        /usr/bin/time -h -o time.txt timeout --foreground 10m python3 "${recomp_verify}" "${n}.tla" "${n}.cfg"
    else
        /usr/bin/time -h -o time.txt timeout --foreground 10m python3 "${recomp_verify}" "${n}.tla" "${n}.cfg" "${flag}"
    fi
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
