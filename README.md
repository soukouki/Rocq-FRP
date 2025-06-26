
# RocqFRP

## English

To build the project, follow the steps below:
1. Run `opam install coq dune`
2. Run `dune build`

If you want to edit using RocqIDE (formerly CoqIDE), additionally run `opam install rocqide`. However, make sure that the versions of Coq and Rocq match.

Currently, both Coq and Rocq need to be installed because dune does not yet support Rocq. Once dune adds support for Rocq in the future, installing Coq will no longer be necessary.

## Japonese

ビルドするには以下の手順を行う。
1. `opam install coq dune`を実行する
2. `dune build`を実行する

RocqIDE(旧CoqIDE)を使って編集する場合には、追加で`opam install rocqide`を実行する。ただし、CoqとRocqのバージョンは同じにすること。

CoqとRocqを両方インストールするのは、現状DuneがRocqに対応していないため。将来的にDuneがRocqに対応すれば、Coqをインストールする必要はなくなる。
