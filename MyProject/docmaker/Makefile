LEC_DIR := ..EE 546/Project/my_project/MyProject/
BUILD_DIR := ./build

SOURCES := Klavins_code.lean

SOURCES     := $(wildcard $(SOURCES)/*.md) 

all: $(SOURCES)
	python ./dm.py $(LEC_DIR)/$@ > $(BUILD_DIR)/$@
