---
name: sv-cleanup
description: Clean up and reorganize SystemVerilog files following coding standards
argument-hint: <file.sv or folder/>
disable-model-invocation: true
allowed-tools: Read, Write, Edit, Glob, Bash(ls *)
---

# SystemVerilog Code Cleanup

Clean up and reorganize SystemVerilog file(s) at: `$ARGUMENTS`

If the argument is a folder, process all `.sv` files in it. If it's a single file, process just that file.

## Cleanup Rules

### 1. Header Comments

The header comment block at the top of the file must follow this format:

```systemverilog
//------------------------------------------------------------------------------
// <Module name and brief description - FIRST LINE>
// <Additional description lines - max 10 lines total for description>
// ...
// Author: <author name>
// Date: <mm/dd/yyyy>
//------------------------------------------------------------------------------
```

Rules:
- **First line**: What this module is/does (required)
- **Description body**: Maximum 10 lines of description (not counting first line, author, date)
- **Second-to-last line**: Author (preserve existing author if present)
- **Last line**: Date in `mm/dd/yyyy` format (convert existing dates to this format)
- Remove excessive historical comments, revision history, or verbose descriptions
- Keep only the essential purpose and key information

### 2. Inline Comments

- **Keep** short inline comments that clarify non-obvious logic
- **Remove** obvious comments like `// increment counter` for `count <= count + 1`
- Inline comments should be concise (ideally < 40 characters)

### 3. Comment Blocks

- **Eliminate** all multi-line comment blocks (`/* ... */`) in the code body
- **Eliminate** large `//` comment blocks (more than 2-3 lines) within the code
- Exception: The header comment block is allowed

### 4. Debug Messages

- **Remove** all debug/simulation-only statements:
  - `$display`, `$write`, `$strobe`, `$monitor`
  - `$info`, `$warning`, `$error`, `$fatal`
  - `$dumpfile`, `$dumpvars`, `$dumpon`, `$dumpoff`
  - `$time`, `$realtime` when used only for debug output
  - `$readmemh`, `$readmemb` if used for test data only
- **Remove** any `initial` blocks that exist solely for debug/test purposes
- **Keep** assertions (`assert`, `assume`, `cover`) unless they are clearly debug-only

### 5. Code Organization

Reorganize the module contents in this exact order:

```systemverilog
module module_name (
    // Port declarations
);

// =============================================================================
// 1. LOGIC DECLARATIONS
// =============================================================================
// All logic, reg, wire, typedef, enum, struct declarations

// =============================================================================
// 2. ASSIGNMENTS
// =============================================================================
// All assign statements and continuous assignments

// =============================================================================
// 3. COMBINATIONAL LOGIC
// =============================================================================
// All always_comb blocks and combinational state machines

// =============================================================================
// 4. SEQUENTIAL LOGIC
// =============================================================================
// All always_ff blocks and sequential state machines

// =============================================================================
// 5. SUBMODULE INSTANTIATIONS
// =============================================================================
// All module instantiations

endmodule
```

Rules for reorganization:
- **Copy-paste exactly**: When moving code blocks, copy-paste them verbatim - do NOT rewrite the logic
- **Combining always blocks**: You may combine multiple `always_ff` or `always_comb` blocks if they share the same sensitivity, but copy-paste the contents exactly without rewriting
- Group related declarations together
- Keep state machine logic together (FSM states, next state logic, output logic)
- Preserve the functional relationship between related code blocks
- Add section headers as shown above (single line, not verbose)
- Remove empty sections if that category has no code

## Processing Steps

1. Read the file(s)
2. Identify and clean up the header comment
3. Remove comment blocks from the code body
4. Trim or remove excessive inline comments
5. Remove debug messages and debug-only initial blocks
6. Reorganize code sections in the specified order (copy-paste, do not rewrite)
7. Write the cleaned file back

## Important

- **Copy-paste, do not rewrite**: When moving or combining code blocks, copy the code exactly as-is - do not rewrite or refactor the logic
- Preserve all functional code - only reorganize, do not change logic
- Maintain proper indentation (use existing file's indentation style)
- Keep parameter and localparam declarations with logic declarations
- Keep generate blocks near the submodule section if they instantiate modules
- If unsure about a comment's value, err on the side of keeping it
