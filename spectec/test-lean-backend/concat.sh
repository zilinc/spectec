#!/bin/bash

separator=";; ──────────────────────────────────────────────────────────────────────────────"

: > "./test-lean-backend/test.spectec"

find "../specification/wasm-3.0" -name "*.spectec" | sort |
while IFS= read -r file; do
    echo "Processing $file"
    cat "$file" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
    echo "$separator" >> "./test-lean-backend/test.spectec"
done