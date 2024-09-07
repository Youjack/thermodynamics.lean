# 形式化热力学——从第零定律到热力学温标

本文基于热源和热力学循环等概念形式化热力学的部分基本概念、定律和定理，主要内容包括：

* 热平衡、热力学第零定律
* 热源
* 热力学循环
* 开尔文表述和克劳修斯表述及其等价性
* 热力学温标

本文有两个目的，一是为初学者提供比常见物理本科热力学教材更严谨的逻辑，二是向物理学研究者展示使用现代软件形式化理论物理的一个例子。本文的所有定义和定理均已通过[Lean 4](https://leanprover-community.github.io)的形式化验证（项目已上传至[GitHub](https://github.com/Youjack/thermodynamics.lean)，本文同时也是这一项目的README）。本文只会提及必要的证明细节，如需了解所有细节，还请阅读Lean代码（但看不懂Lean代码并不妨碍阅读本文）。

> 热力学的公理化（形式化）已经在二十世纪由[Carathéodory](https://zhuanlan.zhihu.com/p/373071679)等人研究过了。但本文采用的是常见热力学教材（如汪志诚的《热力学·统计物理》）中的体系，并不涉及Carathéodory的理论。

## 热力学第零定律

> 本节对应文件[ZerothLaw.lean](https://github.com/Youjack/thermodynamics.lean/blob/master/Thermodynamics/ZerothLaw.lean)

自然界中有许多处于热平衡的系统。“**热平衡**”既可用于描述一个系统的状态，也可以用于描述分别处于热平衡的两个系统（或一个系统中的两个子系统）的相互关系。

```lean
axiom EquilSystem : Type -- 热平衡系统
axiom mutualEquil : EquilSystem → EquilSystem → Prop -- 热平衡关系
```

**热力学第零定律**讲的是：“热平衡”作为（分别处于热平衡的）两个系统的相互关系，满足传递性：若系统A与系统B热平衡，且系统B与系统C热平衡，则系统A与系统C热平衡。我们还默认“热平衡”满足自反性：系统A与系统A热平衡；和对称性：若系统A与系统B热平衡，则系统B与系统A热平衡。

> “热平衡”这种同时满足自反性、对称性和传递性的关系在数学上被称为等价关系。

```lean
axiom mutualEquil.iseqv : Equivalence mutualEquil
```

利用“热平衡”这一等价关系，可以将热平衡系统分类，即，若系统A与系统B热平衡，则系统A与系统B属于同一个类；若系统A与系统B不满足热平衡，则系统A与系统B不属于同一个类。本文将这些类称为“**热源(Reservoir)**”，即一个热源是一系列相互热平衡的系统的集合。在后文中我们将只讨论抽象的“热源”，而不考虑具体的系统。

> 这些由等价关系导出的类在数学上被称为等价类。

```lean
instance EquilSystem.setoid : Setoid EquilSystem :=
  ⟨mutualEquil, mutualEquil.iseqv⟩
def Reservoir := Quotient EquilSystem.setoid
```

对于不满足热平衡的两个热源，我们还要引入“更冷”（或“更热”）的概念，即，两个不满足热平衡的热源中一定有一个热源比另一个热源更冷（或更热）。这一“更冷”的关系应该满足传递性：若热源A比热源B更冷，且热源B比热源C更冷，则热源A比热源C更冷。

> “更冷”这一关系的传递性在数学上意味着“热源”的集合上存在一个线序(linear order)。

```lean
axiom Reservoir.linearOrder : LinearOrder Reservoir
```

## 热力学循环

> 本节对应文件[Cycle.lean](https://github.com/Youjack/thermodynamics.lean/blob/master/Thermodynamics/Cycle.lean)

根据热力学第一定律，“**热力学循环(Cycle)**”可以被抽象成一种热功转换过程，即从一些热源吸热或放热，并消耗或产生功，且满足能量守恒的过程。需要注意的是，这里定义的“热力学循环”并不需要满足热力学第二定律。

```lean
structure Cycle where
  𝓠 : Reservoir →₀ ℝ -- 热量
  𝓦 : ℝ -- 功
  energy_conserv : 𝓠.sum_image - 𝓦 = 0 -- 能量守恒
```

> 这里定义的`Cycle`只从有限多个热源吸/放热。从任意多个热源吸/放热的热力学循环在数学上较为复杂，本文不考虑。

阐述热力学第二定律时，我们需要用到一些特殊的热力学循环。下面将列举这些特殊的循环。

### OneRsvCycle

这是只从一个热源吸/放热的循环。

```lean
structure OneRsvCycle (𝓣 : Reservoir) extends Cycle where
  one_rsv : 𝓠.support = {𝓣}
```

### AbsRelCycle

这是从一个热源吸热，并向另一个热源放热的循环。

```lean
structure AbsRelCycle (𝓐 𝓡 : Reservoir) extends Cycle where
  two_rsv : 𝓠.support = {𝓐, 𝓡} ∧ 𝓐 ≠ 𝓡
  do_abs_rsv : 0 < 𝓠 𝓐 -- 从热源𝓐吸热
  do_rel_rsv : 𝓠 𝓡 < 0 -- 向热源𝓡放热
```

### UsualEngineCycle

这是从一个高温热源吸热，向另一个低温热源放热，并对外做功的循环，这也是教材上常见的动力循环。

```lean
structure UsualEngineCycle {𝓗 𝓒 : Reservoir} (_: 𝓒 < 𝓗) extends (AbsRelCycle 𝓗 𝓒) where
  do_work : 0 < 𝓦
```

### UsualPumpCycle

这是消耗外界的功，并从一个低温热源吸热，然后向另一个高温热源放热的循环，这也是教材上常见的热泵循环（或制冷循环）。

```lean
structure UsualPumpCycle {𝓒 𝓗 : Reservoir} (_: 𝓒 < 𝓗) extends (AbsRelCycle 𝓒 𝓗) where
  do_pump : toCycle.Qabs < toCycle.Qrel
```

## 开尔文表述和克劳修斯表述

> 本节对应文件[SecondLaw.lean](https://github.com/Youjack/thermodynamics.lean/blob/master/Thermodynamics/SecondLaw.lean)

## 热力学温标

> 本节对应文件[Temperature.lean](https://github.com/Youjack/thermodynamics.lean/blob/master/Thermodynamics/Temperature.lean)

根据热力学第一定律，热力学
