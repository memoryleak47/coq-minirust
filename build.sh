#!/bin/bash

[[ ! -d def ]] && echo "You are in the wrong folder!" && exit 1

if [ "$1" == "clean" ]; then
    echo "clearing ..."
    for x in . def proof
    do
        rm -f $x/.*.aux $x/*.vos $x/*.vok $x/*.glob $x/*.vo $x/.makefile.d $x/makefile.conf $x/makefile $x/.Makefile.d $x/Makefile $x/Makefile.conf
    done
    echo "building new Makefile ..."
    coq_makefile -f _CoqProject -o Makefile
elif [ -z "$1" ]; then
    make
else
    echo "build argument not understood!"
fi
