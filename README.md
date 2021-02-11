# Spiral Compiler

Spiralのコンパイラ

### 確認テスト

#### Requirements

事前に以下のインストールが必要です

- Java 11 JRE
- sbt

以下のコマンドでテストが可能です

```
sbt compile
sbt testOnly -- -l org.scalatest.tags.Slow
```

テストの結果，

```
[info] Run completed in 20 seconds, 581 milliseconds.
[info] Total number of tests run: 329
[info] Suites: completed 18, aborted 0
[info] Tests: succeeded 329, failed 0, canceled 0, ignored 0, pending 0
[info] All tests passed.
```

と出ればOK．

### コンパイラの利用

事前準備が必要です．

- 環境変数`SPIRAL_STDLIB_PATH`に`<spiral _dir>/src/test/builtin`を設定
- `sbt assembly`で実行ファイル可能JARを出力
- `<spiral_dir>/bin`に`PATH`を通す

### テストコード

以下は加算モジュールのコード（`Adder.spl`）です．

```
package adder

module Adder
impl Adder {
  input def exec(a: Bit[8], b: Bit[8]) -> Bit[8] {
    a + b
  }
}
```

これをコンパイルするには以下をシェルで実行します．

```
spiral --package adder --top Adder --out Adder.v Adder.spl
```

実行後，Verilog HDLファイルである`Adder.v`が生成されます．