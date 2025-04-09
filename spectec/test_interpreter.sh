#!/bin/bash

for f in ../../spec/test/core/*.wast
do
  echo "---------- $f -----------"
  ./watsup spec/wasm-3.0/* -v -l --interpreter $f
done
