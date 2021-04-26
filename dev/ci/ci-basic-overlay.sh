#!/usr/bin/env bash

# This is the list of repositories used by the CI scripts, unless overridden
# by a call to the "overlay" function in ci-common

declare -a projects # the list of project repos that can be be overlayed

# checks if the given argument is a known project
function is_in_projects {
    for x in "${projects[@]}"; do
      if [ "$1" = "$x" ]; then return 0; fi;
    done
    return 1
}

# project <name> <giturl> <ref> [<archiveurl>]
#   [<archiveurl>] defaults to <giturl>/archive on github.com
#   and <giturl>/-/archive on gitlab
function project {

  local var_ref=${1}_CI_REF
  local var_giturl=${1}_CI_GITURL
  local var_archiveurl=${1}_CI_ARCHIVEURL
  local giturl=$2
  local ref=$3
  local archiveurl=$4
  case $giturl in
    *github.com*) archiveurl=${archiveurl:-$giturl/archive} ;;
    *gitlab*) archiveurl=${archiveurl:-$giturl/-/archive} ;;
  esac

  # register the project in the list of projects
  projects[${#projects[*]}]=$1

  # bash idiom for setting a variable if not already set
  : "${!var_ref:=$ref}"
  : "${!var_giturl:=$giturl}"
  : "${!var_archiveurl:=$archiveurl}"

}

########################################################################
# MathComp
########################################################################
project mathcomp "https://github.com/math-comp/math-comp" "master"

project fourcolor "https://github.com/math-comp/fourcolor" "master"

project oddorder "https://github.com/math-comp/odd-order" "master"

project mczify "https://github.com/math-comp/mczify" "master"

########################################################################
# UniMath
########################################################################
project unimath "https://github.com/UniMath/UniMath" "master"

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq "https://github.com/unicoq/unicoq" "master"

project mtac2 "https://github.com/Mtac2/Mtac2" "master"

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes "https://github.com/coq-community/math-classes" "master"

project corn "https://github.com/coq-community/corn" "master"

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris
# and lambdaRust repos respectively.
project stdpp "https://gitlab.mpi-sws.org/iris/stdpp" ""

project iris "https://gitlab.mpi-sws.org/iris/iris" ""

project autosubst "https://github.com/coq-community/autosubst" "master"

project iris_examples "https://gitlab.mpi-sws.org/iris/examples" "master"

########################################################################
# HoTT
########################################################################
project hott "https://github.com/HoTT/HoTT" "master"

########################################################################
# CoqHammer
########################################################################
project coqhammer "https://github.com/lukaszcz/coqhammer" "master"

########################################################################
# GeoCoq
########################################################################
project geocoq "https://github.com/GeoCoq/GeoCoq" "master"

########################################################################
# Flocq
########################################################################
project flocq "https://gitlab.inria.fr/flocq/flocq" "flocq-3"

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests "https://github.com/coq-community/coq-performance-tests" "master"

########################################################################
# coq-tools
########################################################################
project coq_tools "https://github.com/JasonGross/coq-tools" "master"

########################################################################
# Coquelicot
########################################################################
project coquelicot "https://gitlab.inria.fr/coquelicot/coquelicot" "master"

########################################################################
# Coq-interval
########################################################################
# To revert when upstream maintainer comes back online
# project interval "https://gitlab.inria.fr/coqinterval/interval" "master"
project interval "https://gitlab.inria.fr/egallego/interval" "make+use_dune_for_ocaml"

########################################################################
# Gappa stand alone tool
########################################################################
project gappa_tool "https://gitlab.inria.fr/gappa/gappa" "master"

########################################################################
# Gappa plugin
########################################################################
# To revert when upstream maintainer comes back online
# project gappa "https://gitlab.inria.fr/gappa/coq" "master"
project gappa "https://gitlab.inria.fr/egallego/gappa-coq" "make+use_dune_for_ocaml"

########################################################################
# CompCert
########################################################################
project compcert "https://github.com/AbsInt/CompCert" "master"

########################################################################
# VST
########################################################################
# todo: 2021 03 11: switch back to master once vst merges the compcert3.9 branch
project vst "https://github.com/PrincetonUniversity/VST" "compcert3.9"

########################################################################
# cross-crypto
########################################################################
project cross_crypto "https://github.com/mit-plv/cross-crypto" "master"

########################################################################
# rewriter
########################################################################
project rewriter "https://github.com/mit-plv/rewriter" "master"

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers "https://github.com/mit-plv/fiat" "master"

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto "https://github.com/mit-plv/fiat-crypto" "master"

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy "https://github.com/mit-plv/fiat-crypto" "sp2019latest"

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph "https://github.com/Karmaki/coq-dpdgraph" "coq-master"

########################################################################
# CoLoR
########################################################################
project color "https://github.com/fblanqui/color" "master"

########################################################################
# TLC
########################################################################
project tlc "https://github.com/charguer/tlc" "master-for-coq-ci"

########################################################################
# Bignums
########################################################################
project bignums "https://github.com/coq/bignums" "master"

########################################################################
# coqprime
########################################################################
project coqprime "https://github.com/thery/coqprime" "master"

########################################################################
# bbv
########################################################################
project bbv "https://github.com/mit-plv/bbv" "master"

########################################################################
# bedrock2
########################################################################
project bedrock2 "https://github.com/mit-plv/bedrock2" "tested"

########################################################################
# Equations
########################################################################
project equations "https://github.com/mattam82/Coq-Equations" "master"

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi "https://github.com/LPCIC/coq-elpi" "coq-master"

project hierarchy_builder "https://github.com/math-comp/hierarchy-builder" "coq-master"

########################################################################
# Engine-Bench
########################################################################
project engine_bench "https://github.com/mit-plv/engine-bench" "master"

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm "https://github.com/imdea-software/fcsl-pcm" "master"

########################################################################
# ext-lib
########################################################################
project ext_lib "https://github.com/coq-community/coq-ext-lib" "master"

########################################################################
# simple-io
########################################################################
project simple_io "https://github.com/Lysxia/coq-simple-io" "master"

########################################################################
# quickchick
########################################################################
project quickchick "https://github.com/QuickChick/QuickChick" "master"

########################################################################
# reduction-effects
########################################################################
project reduction_effects "https://github.com/coq-community/reduction-effects" "master"

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib "https://gitlab.inria.fr/fpottier/menhir" "20210310"

########################################################################
# aac_tactics
########################################################################
project aac_tactics "https://github.com/coq-community/aac-tactics" "master"

########################################################################
# paramcoq
########################################################################
project paramcoq "https://github.com/coq-community/paramcoq" "master"

########################################################################
# relation_algebra
########################################################################
project relation_algebra "https://github.com/damien-pous/relation-algebra" "master"

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
project struct_tact "https://github.com/uwplse/StructTact" "master"

project inf_seq_ext "https://github.com/DistributedComponents/InfSeqExt" "master"

project cheerios "https://github.com/uwplse/cheerios" "master"

project verdi "https://github.com/uwplse/verdi" "master"

project verdi_raft "https://github.com/uwplse/verdi-raft" "master"

########################################################################
# stdlib2
########################################################################
project stdlib2 "https://github.com/coq/stdlib2" "master"

########################################################################
# argosy
########################################################################
project argosy "https://github.com/mit-pdos/argosy" "master"

########################################################################
# perennial
########################################################################
project perennial "https://github.com/mit-pdos/perennial" "coq/tested"

########################################################################
# metacoq
########################################################################
project metacoq "https://github.com/MetaCoq/metacoq" "master"

########################################################################
# SF suite
########################################################################
project sf "https://github.com/DeepSpec/sf" "master"

########################################################################
# Coqtail
########################################################################
project coqtail "https://github.com/whonore/Coqtail" "master"

########################################################################
# Deriving
########################################################################
project deriving "https://github.com/arthuraa/deriving" "master"
