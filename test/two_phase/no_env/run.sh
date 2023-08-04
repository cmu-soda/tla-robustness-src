#!/bin/sh

# this will produce an LTS for RM.
java -jar ../../../bin/tlc-ian.jar ResourceManager.tla ResourceManager.cfg

# next, we want to produce the WA for the LTS.
# finally, we want to see if the LTS for TM satisfies the WA for RM.
