#
# @file doc/Makefile
# @brief Makefile for the Achronix SDK documentation
# @details See the README.txt file for more information about building and installing the Achronix SDK.
# @copyright (c) 2022-@showdate "%Y " Achronix Semiconductor Corporation
#

# All recipe is intentionally blank.
# This makefile will be called by the top level Makefile. However this makefile requires doxygen to be
# installed on the users system, so therefore by default doxygen is not called to accommodate users
# who do not have doxygen installed.
all:

# Minimum doxygen version is 1.9.6.
# To regenerate all doxygen html files, the user must execute "make doxygen".
doxygen: Doxygen.cfg
	doxygen Doxygen.cfg

clean distclean:
	$(RM) -r html

install uninstall:

.PHONY: doxygen
