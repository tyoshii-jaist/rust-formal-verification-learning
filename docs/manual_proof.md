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
||| read_obs <= read <= write <= reserve <= max //(not inverted では last は意味をなさない)

// not inverted & reserve wrap
||| reserve < read_obs <= read <= write <= max //(not inverted では last は意味をなさない)

// inverted (write < read_obs) & read not wrap
||| write <= reserve < read_obs <= read <= last <= max

// converted to not inverted by wrapping read 
||| read <= write <= reserve < read_obs <= max //(not inverted では last は意味をなさないが、read_obs がふたをしているので守る必要がある)


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
||| read <= write_obs <= write <= reserve <= max

// not inverted & reserve wrap
||| reserve < read <= write_obs <= write <= max

// converted to inverted by wrapping reserve and write
||| write <= reserve < read <= write_obs <= last <= max

// inverted (write_obs < read) & read not wrap
||| write_obs <= write <= reserve < read <= last_obs == last <= max

ただ、Global の方は上記 Prod/Cons の条件に含まれるので、上記があればよい。

_obs が None のときはどう扱えばよいのか？
 読めている時だけ足せばよさそう。これはすなわち grant や read を行っているときは制約が足されているということを意味しそう。


# Transitions
## Producer
### do_reserve 
reserve := new_reserve

require(
    {
        // not inverted & reserve not wrap
        ||| read_obs <= pre.producer.write <= new_reserve <= pre.length
        // not inverted & reserve wrap
        ||| new_reserve < read_obs <= pre.producer.write <= pre.length
        // inverted (write < read_obs) & read not wrap
        ||| pre.producer.write <= new_reserve < read_obs <= pre.producer.last <= pre.length
        // converted to not inverted by wrapping read 
        ||| pre.producer.write <= new_reserve < read_obs <= pre.producer.last <= pre.length
    }
);

### sub_reserve
reserve := reserve - (len - used)

### update_last_by_write
last := new_last

### update_last_by_max
last := max

### store_write
write := new_write

## Consumer



# Grant/Commit での producer の状態の引き継ぎ
以下を保存して require/ensure で渡す必要がある。
write
reserve
last
read_obs


# Read/Release での consumer の状態の引き継ぎ
read
write_obs
last_obs


# last の遷移について
lenght で初期化される。
write を reserve 位置に移すタイミングで 
- write が wrap する場合で、かつ、write 位置が length でない場合、今の write 位置が last になる。
- reserve (write を持っていく位置) が last 位置を追い抜いていると length に戻す。

