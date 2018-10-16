## 《好耶，是形式验证！》

中文小册子，教 Haskell 初心者写 Agda。

很明显我没有足够仔细地阅读这本书，在这里向广大第一版读者道歉。
续集的发布会带来第一本书的修订版，敬请期待。

希望修订版能完美。

硬伤：

+ 在中文中使用了半角逗号 (P2)
+ Instant Argument -> Instance Argument (P6)
+ `Level` 的定义在 `Agda.Primitive` 里而不是 `Agda.Builtin.Level` (P13)
+ Universal Polymorphism -> Universe Polymorphism (P15)
+ 在代码中使用了宋体的下划线 (P15)
+ 忘记对参数进行模式匹配 (P22)
+ 参数写反了 (P33)

不足：

+ `data Maybe a = Just a | Nothing` -> `data Maybe a = Nothing | Just a` (P8)
+ Universe Polymorphism 可能日后会自动 Generalize (P13)
+ 没有说明 `Setω` (P16)
+ 没有说清楚为什么少生成了一个模式匹配 (P27)
