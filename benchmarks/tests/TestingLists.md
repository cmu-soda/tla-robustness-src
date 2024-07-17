# List of tests for Eduardo when testing recomp-verify and code

In general the following code should be run for the output of the files I am testing:

```
python3 ../../../../../../recomp-verify-pristine/recomp-verify.py [spec].tla [config].tla
python3 ../../../../../bin/recomp-verify.py [spec].tla [config].tla
```
The first line is the original recomp-verify output and the second one is whatever the code compiled by the threading branch.
For testing purposes I have created a new clone of Ian's original recomp-verify and am just using that python file to test the original jar file.

## Two_phase_commit-7
There are two folders: unchanged and wrongtrace which have straightfoward names of what their tests do.
### unchanged
D0 = C1
D1 = T3
D2 = C3
E2 = C2
n: 4
m: 3
WARNING: sun.reflect.Reflection.getCallerClass is not supported. This will impact performance.
k: 3
Total # states checked: 151349
Property satisfied!

### wrongtrace
D0 = C1
D1 = T3
D2 = C3
E2 = C2
n: 4
m: 3
WARNING: sun.reflect.Reflection.getCallerClass is not supported. This will impact performance.
k: 3
Total # states checked: 16
Property may be violated.
Could not confirm the violating trace in the TLA+ spec; this is a bug in the tool.

## lockserv
The following folders to test are lockserv.tla with lockserv.cfg as well as lockserv_incorrect.tla with lockserv_incorrect.cfg
### unchanged
### incorrect

## consesus-for-all-4

### unchanged
### incorrect

### toy_mutex
Nothing special just the normal mutex

### firewall/5
n: 2
m: 0

Component 1: firewall.tla
State space gen: 8264ms
LTS gen: 360ms
# unique states: 56072 states
minimization: 2364ms
# unique states post-minimization: 211 states
WARNING: sun.reflect.Reflection.getCallerClass is not supported. This will impact performance.

k: 0
Total # states checked: 56072
Property satisfied!
 
