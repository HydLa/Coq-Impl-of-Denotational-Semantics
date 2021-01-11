# Coq Implementation of Denotational Semantics

## Requirements
- Macでの動作を想定
- make, docker, docker-compose, xquartzをインストール，設定

## Usage
1. `make`でCoqIDEを起動
1. File -> Openで適当なファイルを開く
1. Compile -> Makeでコンパイル

## Files
### Util.v
本筋と関係なさそうな補題集

### Partial.v
- R上の部分関数 partial := R -> option R
- option R上の引き算，絶対値，比較，割り算
- partialの極限，連続性，繋がり方，微分

### Trajectory.v
- partialの1点更新，区間更新
- 軌道 trajectory := list phase
- trajectoryからpartialへの変換

### PropFormula.v
- Propベースのformulaの定義
- 1つのformulaの閉包，複数のformulaの閉包
- 制約（時間の関数）constraint := list (set formula)
- constraintの閉包
- set formulaの包含関係，constraintの包含関係・比較
- 成立履歴 history := string -> option constraint

### BouncingParticle.v, ParameterizedBouncingParticle.v
- 解集合の計算
