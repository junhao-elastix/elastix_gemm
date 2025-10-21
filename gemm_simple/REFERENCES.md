# Technical Documentation References

**Last Updated**: Mon Oct 20 21:02:35 PDT 2025

## Achronix Speedster7t Documentation

This project leverages several key Achronix technical documents for FPGA development.

### **Core Architecture Documents**

#### **Network-on-Chip (NoC)**
- **File**: [Speedster7t 2D Network on Chip User Guide UG089](../doc/2D_Network_on_Chip/Speedster7t_2D_Network_on_Chip_User_Guide_UG089.html)
- **Usage in Project**: NAP placement strategies, NoC routing, GDDR6 channel topology
- **Key Sections**: NAP types, placement guidelines, performance optimization

#### **Component Library**
- **File**: [Speedster7t Component Library User Guide UG086-1](../doc/Component_Library/Speedster7t_Component_Library_User_Guide_UG086-1.html)
- **Usage in Project**: BRAM configurations, AXI interfaces, synchronizers
- **Key Sections**: Memory components, AXI4 interfaces, clock domain crossing

#### **GDDR6 Memory Integration**
- **File**: [Speedster7t GDDR6 Reference Design Guide RD017](../doc/GDDR6_Reference_Design/Speedster7t_GDDR6_Reference_Design_Guide_RD017.html)
- **Usage in Project**: GDDR6 channel configuration, memory controller setup, performance tuning
- **Key Sections**: Channel topology, training sequences, bandwidth optimization

#### **Soft IP Configuration**
- **File**: [Speedster7t Soft IP User Guide UG103-3](../doc/Soft_IP/Speedster7t_Soft_IP_User_Guide_UG103_3.html)  
- **Usage in Project**: PCIe endpoint configuration, PLL setup, IP parameterization
- **Key Sections**: PCIe Gen5 configuration, memory IP setup, clock generation

---

## Project-Specific Application

### **NoC Architecture (UG089)**
- **NAP Placements**: Channel 0 @ NOC[3][3] for MS2.0 GEMM engine
- **Address Space**: 42-bit addressing for GDDR6 (Page[9] + Address[26] + Offset[7])
- **Routing**: West side placement for optimal Channel 0 access

### **GDDR6 Integration (RD017)**  
- **Channel Configuration**: Single active channel (Channel 0) with 2GB capacity
- **Training**: ADM-based training sequence for GDDR6 initialization
- **Performance**: Target bandwidth optimization for matrix data access

### **Component Usage (UG086-1)**
- **BRAM**: ACX_BRAM72K dual-port configuration for matrix I/O
- **AXI4**: 256-bit data width with burst support for high throughput
- **Synchronizers**: Clock domain crossing for register control

### **IP Configuration (UG103-3)**
- **PCIe**: Gen5 x16 endpoint with 128-register BAR0 mapping
- **PLLs**: Multiple PLL domains (reg_clk, nap_clk, adm_clk)
- **GDDR6 IP**: Single channel configuration with NoC integration

---

## Development Workflow Integration

### **When Designing RTL**
1. **Check NoC Guide (UG089)** for NAP placement best practices
2. **Check Component Library (UG086-1)** for IP usage patterns  
3. **Check GDDR6 Guide (RD017)** for memory interface optimization

### **When Debugging Issues**
1. **NoC routing problems**: Consult UG089 Section 4 (Routing and Congestion)
2. **Memory training failures**: Consult RD017 Section 3 (Training Sequences)
3. **IP configuration errors**: Consult UG103-3 Section 2 (IP Parameters)

### **When Optimizing Performance**
1. **Bandwidth optimization**: RD017 Section 5 (Performance Tuning)
2. **NoC congestion**: UG089 Section 6 (Performance Guidelines)
3. **Component selection**: UG086-1 Section 3 (Resource Usage)

---

## Quick Reference Links

| Topic | Document | Key Sections |
|-------|----------|--------------|
| **NAP Placement** | UG089 | Section 2-3 (NAP Types, Placement) |
| **GDDR6 Setup** | RD017 | Section 2-4 (Configuration, Training) |
| **AXI4 Usage** | UG086-1 | Section 4 (AXI Interfaces) |
| **IP Parameters** | UG103-3 | Section 2-3 (PCIe, Memory IP) |
| **Performance** | RD017 + UG089 | Section 5-6 (Optimization) |

---

This reference guide helps maintain alignment between project implementation and Achronix best practices documented in the official guides.
