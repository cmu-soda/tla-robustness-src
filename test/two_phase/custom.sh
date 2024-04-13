#!/bin/sh

echo "Two Phase Commit"
time python3 ../../../verify.py Monolithic.tla Monolithic.cfg --cust
