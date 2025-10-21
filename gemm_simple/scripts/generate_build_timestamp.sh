#!/bin/bash

# Generate build timestamp for RTL
# This creates a SystemVerilog define for build timestamp

OUTPUT_FILE="../src/include/build_timestamp.svh"

# Generate timestamp in format MMDDHHMI (Month, Day, Hour, Minute)
TIMESTAMP=$(date '+%m%d%H%M')

# Create the include file
cat > "$OUTPUT_FILE" << EOF
// Auto-generated build timestamp - DO NOT EDIT
// Generated on $(date)

\`ifndef BUILD_TIMESTAMP_SVH
\`define BUILD_TIMESTAMP_SVH

\`define BUILD_TIMESTAMP 32'h${TIMESTAMP}

\`endif // BUILD_TIMESTAMP_SVH
EOF

echo "Generated build timestamp: 0x$TIMESTAMP in $OUTPUT_FILE"