#!/bin/bash

for f in ../../spec/test/core/*.wast
do
  echo "---------- $f -----------"
  ./spectec ../specification/wasm-3.0/* -v -l --interpreter $f
done

for f in ../../spec/test/core/simd/*.wast
do
  echo "---------- $f -----------"
  ./spectec ../specification/wasm-3.0/* -v -l --interpreter $f
done
