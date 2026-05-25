#!/bin/bash
cd "$(dirname "$0")"

dune build
mkdir -p results

STRUCTS=(0 1 2)
STRUCT_NAMES=(array ptr map)
OPS=(0 1)
OP_NAMES=(read write)
LEVELS=(0 1)
LEVEL_NAMES=(pub priv)

for s in "${STRUCTS[@]}"; do
  for o in "${OPS[@]}"; do
    for l in "${LEVELS[@]}"; do
      name="${STRUCT_NAMES[$s]}_${LEVEL_NAMES[$l]}_${OP_NAMES[$o]}"
      outfile="results/${name}.txt"

      echo "Running $name ..."

      sed -i \
        -e "s/var test_struct: int@{} = [0-9]/var test_struct: int@{} = $s/" \
        -e "s/var test_op:     int@{} = [0-9]/var test_op:     int@{} = $o/" \
        -e "s/var test_level:  int@{} = [0-9]/var test_level:  int@{} = $l/" \
        sane/benchmark.oio

      ./oblivio.sh sane/config.json &
      SERVER_PID=$!
      sleep 1

      ./oblivio.sh ./sane/benchmark.oio > "$outfile" 2>&1 || true

      kill $SERVER_PID 2>/dev/null || true
      wait $SERVER_PID 2>/dev/null || true

      # wait for port 3050 to be released
      while lsof -ti:3050 > /dev/null 2>&1; do
        kill $(lsof -ti:3050) 2>/dev/null || true
        sleep 0.2
      done

      echo "  done -> $outfile"
    done
  done
done

echo "All benchmarks done."
