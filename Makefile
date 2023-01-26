# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line.
SPHINXOPTS    =
SPHINXBUILD   = python3.8 -m sphinx  # was: sphinx-build
SPHINXPROJ    = cs6501s23
SOURCEDIR     = source
BUILDDIR      = build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

.PHONY: help Makefile

# Setup from Gabriel Ebner (Ack: Thank you for sharing this code. --KS)
VENVDIR := .venv
export PATH := $(VENVDIR)/bin:$(PATH)

install-deps:
	test -f $(VENVDIR)/bin/pip || python3.8 -m venv $(VENVDIR)
	python3.8 -m pip install MarkupSafe>=2.0 sphinx
.PHONY: help Makefile
# python3.8 -m pip install 'wheel>=0.29' # needed for old ubuntu versions, https://github.com/pallets/markupsafe/issues/59

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
