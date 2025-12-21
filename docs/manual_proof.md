# Variables
## Shared variables
write
reserve
last
read

## Local variables
read_obs
write_obs
last_obs

## Constants
max


# Invariants
## Global invariants
read と write の区間 (Consumer占有区間) と write と reserve の間 (Producer占有区間) はdisjoint
// not inverted & reserve not wrap
||| read <= write <= reserve <= last

// not inverted & reserve wrap
||| reserve < read <= write <= last

// inverted (write < read) & read not wrap
||| write <= reserve < read <= last

// inverted (write < read) & read wrap
||| false

## Producer invariants
// not inverted & reserve not wrap
||| read_obs <= read <= write <= reserve <= last

// not inverted & reserve wrap
||| reserve < read_obs <= read <= write <= last

// inverted (write < read_obs) & read not wrap
||| write <= reserve < read_obs <= read <= last

// converted to not inverted by wrapping read 
||| read <= write <= reserve < read_obs <= last


## Consumer invariants
Consumer は write をロードした後に last をロードする。この間に隙があるので、条件が難しい。
思考実験
write を読みだしたときに・・・
1. write < read の場合
この場合、 read <= last になる。
Prod がいくら動いても、last は動かせない。write & reserve が追い越したときにしか last は動かない。

2. write == read の場合
この場合、read は読める領域がない。write は好きに成長できるので、last も今後どうなるかわからない。

3. read < write の場合
この場合、read は write_obs まで成長できるが、本質的に 2 と同じ。

4. write < read == last の場合
この場合、本質的に 1 と同じ。Consumer 側が read を動かさない限り Prod は何もできない。

5. write == read == last の場合
これは本質的に 2, 3 と同じで Prod 側に主導権がある。

6. read < write == last の場合
これも本質的に2,3,5と同じで、Prod 側に主導権がある。

// not inverted (read <= write_obs) & reserve not wrap
||| read <= write_obs <= write <= reserve <= last(last_obs については何も言えない)

// not inverted & reserve wrap
||| reserve < read <= write_obs <= write <= last

// converted to inverted by wrapping reserve and write
||| write <= reserve < read <= write_obs <= last

// inverted (write_obs < read) & read not wrap
||| write_obs <= write <= reserve < read <= last_obs == last

ただ、Global の方は上記 Prod/Cons の条件に含まれるので、上記があればよい。

_obs が None のときはどう扱えばよいのか？
読めている時だけ足せばよいのか。
