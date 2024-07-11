# List of tests for Eduardo when testing recomp-verify and code

In general the following code should be run for the output of the files I am testing:

```
java -jar ../../../../../recomp-verify.jar [spec].tla [config].cfg
java -jar ../../../../bin/recomp-verify.jar [spec].tla [config].cfg
```
The first line is the original recomp-verify output and the second one is whatever the code compiled by the threading branch.

## Two_phase_commit-7
There are two folders: unchanged and wrongtrace which have straightfoward names of what their tests do.
### unchanged
### wrongtrace

## lockserv
The following folders to test are lockserv.tla with lockserv.cfg as well as lockserv_incorrect.tla with lockserv_incorrect.cfg
### unchanged
### incorrect

### toy_mutex
Nothing special just the normal mutex

### firewall/5
 
