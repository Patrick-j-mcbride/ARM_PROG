#!/bin/bash

make realclean
make depend
make

# You will need to change BASETIME if you are not using a Raspberry Pi 2.
# BASETIME is the total time reported by the original C version.
BASETIME=4.613257

TIME=`./regression | grep "Total time" | cut -f 2 -d ':'`

echo Time was $TIME seconds
SPEEDUP=`echo "6 k $BASETIME $TIME / 0.005 + 2 k 1 / p" | dc`
echo "Speedup is $SPEEDUP"
