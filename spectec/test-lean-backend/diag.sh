make

for i in 1 2 3; do

    ./spectec ../specification/wasm-${i}.0/* \
        --print-all-il-to "wasm${i}.0_%s.il" \
        --ite \
        --let-intro-mech \
        --typefamily-removal \
        --remove-indexed-types \
        --totalize \
        --else \
        --else-simplification \
        --uncase-removal \
        --sub-expansion \
        --pattern-simp \
        --sub \
        --definition-to-relation \
        --sideconditions \
        --alias-demut \
        --improve-ids \
        --single-pattern-match
done


for i in 1 2 3; do

    ./spectec ../specification/wasm-${i}.0/* \
        --print-il-as-ast \
        --print-all-il-to "wasm${i}.0_ast_%s.il" \
        --ite \
        --let-intro-mech \
        --typefamily-removal \
        --remove-indexed-types \
        --totalize \
        --else \
        --else-simplification \
        --uncase-removal \
        --sub-expansion \
        --pattern-simp \
        --sub \
        --definition-to-relation \
        --sideconditions \
        --alias-demut \
        --improve-ids \
        --single-pattern-match
done
