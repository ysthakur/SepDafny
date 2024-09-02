HWNAME      := hw05
COURSE      := cis5520
SEMESTER    := 22fa

DESCRIPTION := State Monad and Applicative Parsing

SUBMIT      := src/LuParser.hs src/LuStepper.hs src/LuSyntax.hs

SOURCES     := src/LuSyntax.lhs src/LuParser.lhs src/LuStepper.lhs 

EXTRA       := lu/*.lu src/State.hs src/Parser.hs src/Main.hs

TESTSRC     := test/Main.hs lu/*.lu src/State.hs src/Parser.hs $(EXTRA)

URL         ?= $(subst ",,http://www.cis.upenn.edu/~$(COURSE)/$(SEMESTER)/hw/$(HWNAME)/HW05.html)

include ../../../haskelltester/hw.mk
include ../hwsite.mk

