LEC_DIR := ../
BUILD_DIR := ./build

SOURCES := Klavins_code.lean

SOURCES     := $(wildcard $(SOURCES)/*.md) 

all: $(SOURCES)
	python ./dm.py $(LEC_DIR)/$@ > $(BUILD_DIR)/$@
