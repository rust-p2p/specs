#!/usr/bin/env python3

import argparse
import pathlib
import os
import sys

parser = argparse.ArgumentParser(description='tlc wrapper')
parser.add_argument('module', type=str, help='the module to check')
parser.add_argument('--coverage', action='store_true', help='enable coverage report')
parser.add_argument('--states', action='store_true', help='dumps states')
parser.add_argument('--dot', action='store_true', help='export states to graphviz')
args = parser.parse_args()

root = os.getcwd()
libraries = []
modules = {}
tla_java_opts = '-DTLA-Library='
coverage = ''
dump = ''

for file in pathlib.Path(root).rglob('*.tla'):
    lib = os.path.dirname(file)
    if not lib in libraries:
        libraries.append(lib)
        tla_java_opts += lib + ':'

for file in pathlib.Path(root).rglob('*.cfg'):
    mod = os.path.basename(file)[:-4]
    modules[mod] = os.path.dirname(file)

if not args.module in modules:
    print('module not found')
    print(list(modules.keys()))
    sys.exit()

wdir = modules[args.module]

if args.coverage:
    coverage += '-coverage 0 '

if args.states:
    dump += '-dump ' + wdir + '/' + args.module + '.states '

if args.dot:
    dump += '-dump dot,colorize,actionlabels ' + wdir + '/' + args.module + '.states '

cmd = 'tlc ' + coverage + dump + args.module + '.tla'

os.environ['TLA_JAVA_OPTS'] = tla_java_opts
os.chdir(wdir)
os.system(cmd)
