# ---------------------------------------------------------------------
#
# Copyright (c) 2021 Achronix Semiconductor Corp.
# All Rights Reserved.
#
# This Software constitutes an unpublished work and contains
# valuable proprietary information and trade secrets belonging
# to Achronix Semiconductor Corp.
#
# Permission is hereby granted to use this Software including
# without limitation the right to copy, modify, merge or distribute
# copies of the software subject to the following condition:
#
# The above copyright notice and this permission notice shall
# be included in in all copies of the Software.
#
# The Software is provided “as is” without warranty of any kind
# expressed or implied, including  but not limited to the warranties
# of merchantability fitness for a particular purpose and non-infringement.
# In no event shall the copyright holder be liable for any claim,
# damages, or other liability for any damages or other liability,
# whether an action of contract, tort or otherwise, arising from, 
# out of, or in connection with the Software
#
#
# ---------------------------------------------------------------------
# Description : Place and route reference design makefile
# ---------------------------------------------------------------------

# Define the top level module
TOP_LEVEL_MODULE :=elastix_gemm_top

# Set path to /src directory relative to this file
SRC_DIR := ../src
# Set filelist name. Path relative to the generated results directory
FILELIST_NAME := ../../../src/filelist.tcl

# Output bitstream path is relative to this directory
OUTPUT_BITSTREAM_PATH := ../demo/bitstream

# Set whether to generate ioring files
# Options are yes, no and only.  Note that "only" is the same as running make ioring_only
GENERATE_IORING := "no"

# Set whether to generate two stage bitstream files
# Options are yes and no.
GENERATE_TWO_STAGE_BITSTREAM := "no"

#------------------------------------------------------------
# Calcuate bitstream version numbers
#------------------------------------------------------------
MAJOR_VERSION := $(shell grep ACX_MAJOR_VERSION ../src/include/version_defines.svh | cut -d " " -f 3)
MINOR_VERSION := $(shell grep ACX_MINOR_VERSION ../src/include/version_defines.svh | cut -d " " -f 3)
$(info MAJOR_VERSION = $(MAJOR_VERSION). MINOR_VERSION = $(MINOR_VERSION))

#------------------------------------------------------------
# Following variables define the device and technology
#------------------------------------------------------------
TECHNOLOGY := "AchronixSpeedster7t"

# ------------------------------
# If targeting Speedster7t 7t1500 device, enable the lines below
# If using a Speedcore, disable this section
# ------------------------------
# Device currently supported; AC7t1500, AC7t1400
DEVICE     := "AC7t1500"
DEVICE_ACE := $(DEVICE)
PACKAGE    := "F53"

# ------------------------------
# If targeting a Speedcore device, enable this section
# and disable the section above
# Note : Speedcore devices do not have the hard interface
# IP, nor do they contain the NOC or NAPs.
# ------------------------------
# DEVICE     := "AC7tFSC04A500"
## ACE requires the R1 suffix on a Speedcore device
# DEVICE_ACE := "${DEVICE}R1"
# PACKAGE    := "CORE"

# ------------------------------
# Set desired Speed Grade
# ------------------------------
# Can be overridden by ace_options.tcl
SPEED_GRADE := "C1"

# -------------------------------------------------------
# Set number of parallel jobs if multiprocess is selected
# -------------------------------------------------------
PARALLEL_JOBS := 4

# ------------------------------
# Set output directory base
# ------------------------------
OUTDIR := results

# ---------------------------------------------------------------------
# Build timestamp header generation
# ---------------------------------------------------------------------
GEN_HEADER := ../src/include/build_timestamp.svh
BUILD_TIMESTAMP_HEX := $(shell date +%m%d%H%M)

.PHONY : gen_build_info
gen_build_info :
	@echo "\`ifndef ACX_BUILD_TIMESTAMP" > $(GEN_HEADER)
	@echo "\`define ACX_BUILD_TIMESTAMP 32'h$(BUILD_TIMESTAMP_HEX)" >> $(GEN_HEADER)
	@echo "\`endif" >> $(GEN_HEADER)
	@echo "Generated $(GEN_HEADER) with ACX_BUILD_TIMESTAMP=32'h$(BUILD_TIMESTAMP_HEX)"

# ---------------------------------------------------------------------
# Should not need to edit below here
# ---------------------------------------------------------------------

# Dervied directory names
ACE_BUILD_DIR := $(OUTDIR)/ace
SYN_BUILD_DIR := $(OUTDIR)/syn

# ---------------------------------------------------------------------
# Following variables define the build environment
# ---------------------------------------------------------------------

# Set $REV_DIR = "ace" for integrated ACE synthesis by default, ACE 10.0 onwards
# Set $REV_DIR to another value, i.e. rev_1, to use separate standalone synthesis by default
# To override the default setting of REV_DIR, use the run_ss receipe
REV_DIR  := ace

# ACE implementation directory.
IMPL_DIR := impl_1

# Set the target netlist based on whether the build will use integrated or standalone synthesis
# When using ACE integrated synthesis, there is no dependency on the target netlist, as ACE will
# generate it.  So the target is set to blank
# As an FYI, the netlist produced by ACE is as defined below
# ACE_NETLIST := $(ACE_BUILD_DIR)/$(IMPL_DIR)/syn/rev_acx/$(TOP_LEVEL_MODULE)_$(IMPL_DIR).vm
ifeq ($(REV_DIR),ace)
    TARGET_NETLIST :=
else
    TARGET_NETLIST := $(SYN_BUILD_DIR)/$(REV_DIR)/$(TOP_LEVEL_MODULE).vm
endif
# ---------------------------------------------------------------------
# Makefile default, full run with generation of ioring files
# ---------------------------------------------------------------------
all :
	$(MAKE) run GENERATE_IORING=yes

# ---------------------------------------------------------------------
# Pattern rules
# ---------------------------------------------------------------------

# The % matches the project names and makes this a pattern rule
# ACE will always generate a timing_routed file, make this file dependent upon the input netlist
$(ACE_BUILD_DIR)/$(IMPL_DIR)/pnr/reports/$(TOP_LEVEL_MODULE)_timing_routed*.html : $(TARGET_NETLIST) $(SRC_DIR)/constraints/*.pdc $(SRC_DIR)/constraints/*.sdc | make_dirs
	@(if [ -d "$(ACE_BUILD_DIR)" ] ; then \
	    cd $(ACE_BUILD_DIR) ;\
	    ace -batch -script_file ../../../scripts/create_ace_project.tcl -script_args "$(TOP_LEVEL_MODULE) $(FILELIST_NAME) $(REV_DIR) $(IMPL_DIR) $(DEVICE_ACE) $(SPEED_GRADE) $(MULTIPROCESS) $(PARALLEL_JOBS) $(GENERATE_IORING) $(GENERATE_TWO_STAGE_BITSTREAM)" ;\
	else \
	    echo "ERROR - failed to run ACE" \
	    echo "No such directory $(ACE_BUILD_DIR)" ;\
	fi ;\
	)

# Synthesis output is dependent upon source files
$(SYN_BUILD_DIR)/$(REV_DIR)/$(TOP_LEVEL_MODULE).vm : $(SRC_DIR)/rtl/*.v $(SRC_DIR)/rtl/*.sv $(SRC_DIR)/constraints/*.sdc $(SRC_DIR)/constraints/*.fdc $(SRC_DIR)/constraints/synplify_options.tcl | make_dirs
	@(if [ "$(REV_DIR)" != "ace" ] ; then \
		if [ -d "$(SYN_BUILD_DIR)" ] ; then \
		    cd $(SYN_BUILD_DIR) ;\
		    synplify_pro -batch ../../../scripts/create_synth_project.tcl $(TOP_LEVEL_MODULE) $(FILELIST_NAME) $(REV_DIR) $(TECHNOLOGY) $(DEVICE) $(SPEED_GRADE) $(PACKAGE) ;\
		else \
		    echo "ERROR - failed to run Synplify Pro" ;\
		    echo "No such directory ./$(SYN_BUILD_DIR)" ;\
		fi ;\
	else \
	    echo "Standalone Synplify Pro not run. Using ACE integrated synthesis" ;\
	fi ;\
	)

# ---------------------------------------------------------------------
# Individual rules to build each flow of the full test
# ---------------------------------------------------------------------

# Do place and route using ACE.  Makes use of the file pattern rule above
# Dependent upon final copied bitstream
.PHONY : pnr
pnr : $(ACE_BUILD_DIR)/$(IMPL_DIR)/pnr/output/$(TOP_LEVEL_MODULE).hex

# Do evaluation mode place and route. Dependency is routed timing file
.PHONY : pnr_eval
pnr : $(ACE_BUILD_DIR)/$(IMPL_DIR)/pnr/reports/$(TOP_LEVEL_MODULE)_timing_routed*.html

# Run synthesis
.PHONY : synthesis
synthesis : $(SYN_BUILD_DIR)/$(REV_DIR)/$(TOP_LEVEL_MODULE).vm

# By default, multiprocess is turned off
MULTIPROCESS = 0

# ---------------------------------------------------------------------
# Default flow.
# ---------------------------------------------------------------------
run : gen_build_info synthesis pnr copy_bitstream

# ---------------------------------------------------------------------
# Default flow with multiprocess, (mp)
# ---------------------------------------------------------------------
run_mp : 
	$(MAKE) run MULTIPROCESS=1

# ---------------------------------------------------------------------
# Default flow to run with standalone synthesis, (ss)
# ---------------------------------------------------------------------
run_ss : 
	$(MAKE) run REV_DIR=rev_1

# ---------------------------------------------------------------------
# Default flow with two stage bitstream generation
# ---------------------------------------------------------------------
#run_two_stage : 
#	$(MAKE) run GENERATE_TWO_STAGE_BITSTREAM=yes copy_two_stage_bitstream

# ---------------------------------------------------------------------
# Only generate ioring files
# ---------------------------------------------------------------------
ioring_only : make_dirs
	@(if [ -d "$(ACE_BUILD_DIR)" ] ; then \
	    cd $(ACE_BUILD_DIR) ;\
	    ace -batch -script_file ../../../scripts/create_ace_project.tcl -script_args "$(TOP_LEVEL_MODULE) $(FILELIST_NAME) $(REV_DIR) $(IMPL_DIR) $(DEVICE_ACE) $(SPEED_GRADE) $(MULTIPROCESS) $(PARALLEL_JOBS) only" ;\
	else \
	    echo "ERROR - failed to run ACE" \
	    echo "No such directory $(ACE_BUILD_DIR)" ;\
	fi ;\
	)


# ---------------------------------------------------------------------
# Synthesis only
# ---------------------------------------------------------------------
syn_only : synthesis

# ---------------------------------------------------------------------
# Place and route only
# ---------------------------------------------------------------------
pnr_only : pnr

# Output bitstream dependencies

# ACE hex file is dependent upon timing file.  Timing file is produced in both eval and normal flow modes
$(ACE_BUILD_DIR)/$(IMPL_DIR)/pnr/output/$(TOP_LEVEL_MODULE).hex : $(ACE_BUILD_DIR)/$(IMPL_DIR)/pnr/reports/$(TOP_LEVEL_MODULE)_timing_routed*.html

# Make copy_bitstream use wildcards to copy any hex, flash or pcie file to the output bitstream folder, with version number
# Make dependent upon ACE hex file generation
.PHONY : copy_bitstream
copy_bitstream : $(ACE_BUILD_DIR)/$(IMPL_DIR)/pnr/output/$(TOP_LEVEL_MODULE).hex
	@if [ ! -d "$(OUTPUT_BITSTREAM_PATH)" ] ; then mkdir $(OUTPUT_BITSTREAM_PATH); fi; \
	for EXT in hex flash pcie; do \
	    for PROG_FILE in `find $(ACE_BUILD_DIR)/$(IMPL_DIR) -name "*.$$EXT"`; do \
	        BASE_NAME=$$(basename -- $${PROG_FILE%.*}); \
	        cp $(ACE_BUILD_DIR)/$(IMPL_DIR)/pnr/output/$$BASE_NAME.$$EXT $(OUTPUT_BITSTREAM_PATH)/$$BASE_NAME.VP815.$(MAJOR_VERSION).$(MINOR_VERSION).$$EXT ; \
	        echo "Copied $$BASE_NAME.$$EXT to $(OUTPUT_BITSTREAM_PATH)/$$BASE_NAME.VP815.$(MAJOR_VERSION).$(MINOR_VERSION).$$EXT" ; \
	    done \
	done

# Include copying mem_init_files to the output directory, so that paths to files are maintained.
make_dirs :
	@if [ ! -d "$(OUTDIR)" ] ; then mkdir $(OUTDIR); fi;
	@cd $(OUTDIR); if [ ! -d ace ] ; then mkdir ace; fi;
	@cd $(OUTDIR); if [ ! -d syn ] && [ "$(REV_DIR)" != "ace" ] ; then mkdir syn; fi;
	@cd $(OUTDIR); if [ -d ../../src/mem_init_files ] ; then cp -Rf ../../src/mem_init_files .; fi;

clean:
	@rm -rf $(OUTDIR)

