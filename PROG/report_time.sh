#!/bin/bash

make realclean
make depend
make

# You will need to change BASETIME if you are not using a Raspberry Pi 2.
# BASETIME is the total time reported by the original C version.
BASETIME=23.842752

TIME=`./regression | grep "Total time" | cut -f 2 -d ':'`

echo Time was $TIME seconds
