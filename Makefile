################################################################################
# Tools & Input config
################################################################################

CXX=g++
RM=rm -rf
BOOST=-lboost_regex
CPPFLAGS=-std=c++17
CONFIG=./config/config_gr.json

################################################################################
# Commands generating executable files
################################################################################

GENSMTINPUT_SRC=./src/genSMTInput.cpp ./src/obj.cpp ./src/graph.cpp ./src/dbConfig.cpp ./src/SMTCell.cpp ./src/flow.cpp ./src/design_rule.cpp ./src/placement.cpp ./src/layoutParser.cpp
GENTESTCASE_SRC=./src/genTestCase.cpp ./src/obj.cpp
CONVSMTRESULT_SRC=./src/convSMTResult.cpp ./src/obj.cpp ./src/graph.cpp ./src/SMTCell.cpp

all: genSMTInput genTestCase convSMTResult

genSMTInput: ./src/genSMTInput.cpp
	$(CXX) $(CPPFLAGS) -o genSMTInput $(GENSMTINPUT_SRC)

genTestCase: ./src/genTestCase.cpp
	$(CXX) $(CPPFLAGS) -o genTestCase $(GENTESTCASE_SRC)

convSMTResult: ./src/convSMTResult.cpp
	$(CXX) $(CPPFLAGS) -o convSMTResult $(CONVSMTRESULT_SRC) $(BOOST)

clean:
	$(RM) genSMTInput genTestCase convSMTResult

################################################################################
# Commands to recompile		       
################################################################################

recompile:
	make clean
	make all

recompile_genSMTInput:
	make clean
	make genSMTInput

