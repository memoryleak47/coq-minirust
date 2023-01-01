#!/bin/bash

[[ ! -d def ]] && echo "You are in the wrong folder!" && exit 1

if [ "$1" == "clean" ]; then
    echo "clearing ..."
    rm -f $(find . -regex '.*\.\(vos\|vok\|vo\|glob\|aux\)$')
    rm -f Makefile Makefile.conf

    echo "building new Makefile ..."
    coq_makefile -f _CoqProject -o Makefile
elif [ -z "$1" ]; then
    make
else
    echo "build argument not understood!"
fi
