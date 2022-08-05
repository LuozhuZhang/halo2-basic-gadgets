use std::{marker::PhantomData, default, iter::Map};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::*,
    plonk::*, poly::Rotation,
    // 定义curve: https://docs.rs/pasta_curves/0.4.0/pasta_curves/index.html
    pasta::Fp, dev::MockProver,
};

// 在region.assign_advice中，如果成功就返回AssignedCell，如果失败就返回Error
#[derive(Debug, Clone)]
struct ACell<F: FieldExt>(AssignedCell<F, F>);

#[derive(Debug, Clone)]
// * 1.Config
struct FiboConfig {
    // 在这里定义advice column的数量
    pub advice: [Column<Advice>; 3],
    pub selector: Selector,
}

struct FiboChip<F: FieldExt> {
    config: FiboConfig,
    // marker在这里并没有实际意义，只不过假装用到了parameter F，防止compiler报错
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FiboChip<F> {
    // 这是一个function（关联函数），返回实例自身
    // 传入FiboConfig struct，返回FiboChip
    pub fn construct(config: FiboConfig) -> Self {
        Self { config, _marker: PhantomData }
    }

    // 输入ConstraintSystem，返回FiboConfig
    // ConstraintSystem必须要带一个参数<F>
    // 不是方法的关联函数，常作为返回一个结构体新实例的构造函数

    // configure是实际写circuit的地方，我们在这里定义custom gate等
    
    // * 注意：我们这里采用了第二种写法，把columns放到 MyCircuit 的 configure 函数里面定义
    // * 这样做的好处就是可以复用columns，传到不同的Chip里
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 3],
        instance: Column<Instance>,
    ) -> FiboConfig {
        // ConstraintSystem主要做电路约束，里面有许多重要的API：https://docs.rs/halo2_proofs/latest/halo2_proofs/plonk/struct.ConstraintSystem.html
        // 比如 create_gate 和 advice_column 等，用meta作为parameter-argument来调用
        let col_a = advice[0];
        let col_b = advice[1];
        let col_c = advice[2];
        let selector = meta.selector();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta: &mut VirtualCells<F>| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //

            // 这里的query也可以叫select，根据一个column得到里面的cell
            // 这里query出selector column
            let s: Expression<F> = meta.query_selector(selector);
            let a: Expression<F>  = meta.query_advice(col_a, Rotation::cur());
            let b: Expression<F> = meta.query_advice(col_b, Rotation::cur());
            let c: Expression<F>  = meta.query_advice(col_c, Rotation::cur());

            // return constraint
            // 让这个constraint = 0，所以可以enable selector
            vec![s * (a + b - c)];
        });

        // 写好circuit gate之后，就可以return了
        FiboConfig { 
            advice: [col_a, col_b, col_c],
            selector,
            instance,
        }

    // fn assign()
    }

    // 这里定义的是在Fibochip impl context下的method
    // 输入两个table中的private input，就是a和b
    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
        a: Option<F>,
        b: Option<F>
    ) -> Result<(ACell<F>, ACell<F>, ACell<F>), Error>{
        // layouter应该就是主要用来fed数据
        // * Layouter lays out regions in the table
        // * region可以理解为分配约束在table中使用的空间：https://docs.google.com/presentation/d/1HUJPHXaqbmVsnmI331mJn9nRuZkeHQZkIMpWBOJ1itk/edit#slide=id.p7
        layouter.assign_region(
            || "first row",
            |mut region| {
                // 打开第一行的selector
                // offset算是一种relative的位置
                self.config.selector.enable(&mut region, offset: 0)?;

                // assign第一个a cell（就是a0）
                // assign_advice最终返回assignedCell或者Error
                let a_cell = region.assign_advice(
                    // 命名
                    annotation: || "a",
                    // 第几个advice column
                    column: self.config.advice[0],
                    // 没有relative location
                    offset: 0,
                    // 错误处理
                    to: || a.ok_or(Error::Synthesis),
                ).map(op: ACell)?;

                let b_cell = region.assign_advice(
                    annotation: || "b",
                    column: self.config.advice[1],
                    offset: 0,
                    to: || a.ok_or(Error::Synthesis),
                ).map(op: ACell)?;

                // a + b = c
                let c_val: Option<F> = a.and_then(|a| b.map(|b| a + b));

                let c_cell = region.assign_advice(
                    annotation: || "c",
                    column: self.config.advice[2],
                    offset: 0,
                    to: || a.ok_or(Error::Synthesis),
                ).map(op: ACell)?;

                // 返回一个带值的tuple，就是最终assigned的region
                Ok((a_cell, b_cell, c_cell))

                // * 所有copy constraint的作用在这里就格外明显
                // * 我们只需要定义first row的cells，就可以复制粘贴给所有的rows
                // * insert copy constraint
            };
        )
    }

    fn assign_row(&self, mut layouter: impl Layouter<F>, prev_b: &ACell<F>, prev_c: &ACell<F>)
        // 只需要return最后一个cell（c）
        -> Result<ACell<F>, Error> {
            layouter.assign_region(
                || "next row",
                |mut region: Region<F>| {
                    self.config.selector.enable(&mut region, offset: 0);

                    // 所以要copy之前的b和c，给后面的b和c（为什么少了a呢？）
                    // 搞懂了，因为permutation的时候有一个置换，第一行的b变成了下一行的a
                    prev_b.0.copy_advice(annotation: || "a", &mut region, column: self.config.advice[0], offset: 0)?;
                    prev_c.0.copy_advice(annotation: || "b", &mut region, column: self.config.advice[1], offset: 0)?;
                
                    let c_val = prev_b.0.value().and_then(
                        |b| {
                            prev_c.0.value().map(|c| *b + *c)
                        }
                    )

                    let c_cell: ACell<F> = region.assign_advice(
                        annotation: || "c",
                        column: self.config.advice[2],
                        offset: 0,
                        to: || c.ok_or(err: Error::Synthesis),)
                    }.map(op: ACell)?;

                    Ok(c_cell);
            )
    } 
}

#[derive(Default)]
struct MyCircuit<F> {
    pub a: Option<F>,
    pub b: Option<F>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = FiboConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector = meta.selector();
        FiboChip::configure(meta, [col_a, col_b, col_c], selector)
        // 这里就会返回FiboConfig -> Config -> FiboConfig
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        // 实例化？
        // 我们会复用这个chip，来design许多东西
        // construct里面主要是FibConfig，里面定义了我们需要的columns数量
        let chip = FiboChip::construct(config);
        
        // assign
        let ( prev_a, mut prev_b, prev_c) = chip.assign_first_row(
            // namespace主要作用就是传入一个name
            // 在circuit::Layouter：https://docs.rs/halo2_proofs/0.2.0/halo2_proofs/circuit/trait.Layouter.html
            layouter.namespace(|| "first row"),
            self.a, self.b,
        );

        // Given f(0)=x, f(1)=y, we will prove f(9)=z
        for _i in 3..10 {
            // 在这里可以把table的其余row都assign
            let c_cell = chip.assign_row(
                layouter.namespace(name_fn: || "next row"),
                &prev_b,
                &prev_c,
            )
            prev_b = prev_c;
            prev_c = c_cell;
        }

        Ok(())
    }
}

// 在这里实例化一个circuit
// 可以传入一些真实值做测试
fn main() {
    let k = 4;
    // Fp上的元素
    let a = Fp::from(1);    // F[0]
    let b = Fp::from(1);    // F[1]
    let out = Fp::from(55); // F[9]

    // 实例化一个circuit
    let circuit = MyCircuit {
        a: Some(a),
        b: Some(b),
    };

    // 创造一个prover，用来做测试
    let prover = MockProver::run(k, &circuit, vec![].unwrap());
    prover.assert_satisfied();
}
