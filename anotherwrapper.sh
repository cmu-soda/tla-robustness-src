#!/usr/bin/env bash

# Usage: ./master.sh <spec_name>

if [ $# -lt 1 ]; then
    echo "Wrong usage!"
    echo "Usage: $0 <base_name_of_spec>"
    echo "Example: $0 two_phase_commit"
    exit 1
fi

spec_name="$1"
orig_dir="$(pwd)"

# Print the variables
echo "Base name of the spec (spec_name): $spec_name"
echo "Original directory (orig_dir): $orig_dir"

# Run the parallel decomposition once to generate the out/* directories and custom_recomp.csv files
python3 ~/Research/REU/recomp-verify/recomp-verify.py "${spec_name}.tla" "${spec_name}.cfg" --parallel

# Copy the TLA, CFG, and no_invs.cfg files
# quick comment: I don't know why I need to copy the no_invs.cfg file (it just breaks when I don't)
cp "${spec_name}.tla" "${spec_name}.cfg" no_invs.cfg out/cust_1/
cp "${spec_name}.tla" "${spec_name}.cfg" no_invs.cfg out/cust_2/
cp "${spec_name}.tla" "${spec_name}.cfg" no_invs.cfg out/mono/
cp "${spec_name}.tla" "${spec_name}.cfg" no_invs.cfg out/naive/

# cust_1.sh
cat > cust_1.sh <<EOF
#!/usr/bin/env bash

echo "Running cust_1.sh"
echo "Base name of the spec is: ${spec_name}"
echo "Original directory is: ${orig_dir}"

# Navigate to the target directory
cd "${orig_dir}/out/cust_1" || {
    echo "Failed to cd into the target directory." >&2
    exit 1
}

# Run the verification script with the --cust option
python3 "/Users/eddie/Research/REU/recomp-verify/recomp-verify.py" \\
    "${spec_name}.tla" \\
    "${spec_name}.cfg" \\
    --cust > "cust_1.log" 2>&1
EOF

# cust_2.sh
cat > cust_2.sh <<EOF
#!/usr/bin/env bash

echo "Running cust_2.sh"
echo "Base name of the spec is: ${spec_name}"
echo "Original directory is: ${orig_dir}"

# Navigate to the target directory
cd "${orig_dir}/out/cust_2" || {
    echo "Failed to cd into the target directory." >&2
    exit 1
}

# Run the verification script with the --cust option
python3 "/Users/eddie/Research/REU/recomp-verify/recomp-verify.py" \\
    "${spec_name}.tla" \\
    "${spec_name}.cfg" \\
    --cust > "cust_2.log" 2>&1
EOF

# mono.sh
cat > mono.sh <<EOF
#!/usr/bin/env bash

echo "Running mono.sh"
echo "Base name of the spec is: ${spec_name}"
echo "Original directory is: ${orig_dir}"

# Navigate to the target directory
cd "${orig_dir}/out/mono" || {
    echo "Failed to cd into the target directory." >&2
    exit 1
}

# Run the verification script with the --cust option
python3 "/Users/eddie/Research/REU/recomp-verify/recomp-verify.py" \\
    "${spec_name}.tla" \\
    "${spec_name}.cfg" \\
    --cust > "mono.log" 2>&1
EOF

# naive.sh
cat > naive.sh <<EOF
#!/usr/bin/env bash

echo "Running naive.sh"
echo "Base name of the spec is: ${spec_name}"
echo "Original directory is: ${orig_dir}"

# Navigate to the target directory
cd "${orig_dir}/out/naive" || {
    echo "Failed to cd into the target directory." >&2
    exit 1
}

# Run the verification script with the --naive option
python3 "/Users/eddie/Research/REU/recomp-verify/recomp-verify.py" \\
    "${spec_name}.tla" \\
    "${spec_name}.cfg" \\
    --naive > "naive.log" 2>&1
EOF

# Make the scripts executable
chmod +x cust_1.sh cust_2.sh mono.sh naive.sh

echo "./cust_1.sh"
echo "./cust_2.sh"
echo "./mono.sh"
echo "./naive.sh"

parallel --halt now,done=1 --line-buffer --keep-order ::: \
    "./mono.sh" \
    "./cust_1.sh" \
    "./cust_2.sh" \
    "./naive.sh"
