#!/bin/bash

NoColour='\033[0m'        # Text Reset
Red='\033[0;31m'          # Red
Green='\033[0;32m'        # Green

count=0
fail_count=0

dirs=("../../spec/test/core" "../../spec/test/core/simd")

for dir in "${dirs[@]}"; do
  for f in $dir/*.wast; do
    ((count++))
    echo "---------- $f -----------"
    ./spectec ../specification/wasm-3.0/* --interpreter $f
    res=$?
    if [[ $res -ne 0 ]];
    then ((fail_count++))
    fi
  done
done


# The summary doesn't work, as the SpecTec interpreter returns 0 all the time.

# if [[ $count -eq 0 ]]; then
#   echo -e "${Red}Summary: No tested found!${NoColour}";
# elif [[ $count -gt 0 && $fail_count -gt 0 ]]; then
#   echo -e "${Red}Summary: $count tested; $fail_count failed!${NoColour}";
#   exit 1
# else
#   echo -e "${Green}Summary: $count tested; all passed!${NoColour}";
#   exit 0
# fi
# 