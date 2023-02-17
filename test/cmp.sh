#!/bin/sh

tlcian_jar="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/bin/tlc-ian.jar"
tlc_jar="/Users/idardik/bin/tla2tools.jar"

module1="$1"
module2="$2"
output="$3"

if [[ "${module1}" = "" ||  "${module2}" = "" || "${output}" = "" ]]
then
    echo "usage: cmp.sh <module1> <module2> <output>"
    exit
fi


# generate err pre and err post comparison files
mkdir -p "${output}"
java -jar "${tlcian_jar}" "${module1}.tla" "${module1}.cfg" "${module2}.tla" "${module2}.cfg" "${output}"
rm -rf states/
rm -f "${module}_TTrace"*


# run comparison
pushd "${output}"

echo "running error pre"
java -jar "${tlc_jar}" -deadlock -config Combined_ErrPre.cfg Combined_ErrPre.tla

echo ""
echo "running error post"
java -jar "${tlc_jar}" -deadlock -config Combined_ErrPost.cfg Combined_ErrPost.tla

rm -rf states/
rm -f "${module}_TTrace"*
popd
