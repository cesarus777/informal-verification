# Build

``` sh
cmake -B build -S .
cmake --build build
```

# Generate trace

``` sh
./build/tests 1000 # or another number of threads
```

# Verify

``` sh
python3 spot-verifier.py trace.log model.hoa
```
