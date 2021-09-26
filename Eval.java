import ast.*;
import picocli.CommandLine;

import java.util.*;
public class Eval extends BaseEval {
    //-----------------------!! DO NOT MODIFY !!-------------------------
    private int[][] M;

    public Eval(int[][] M) {
        this.M = M;
    }
    //-------------------------------------------------------------------

    private static void sort(int[] a, int low, int high) {
        int p, i, j, tmp;
        if (low >= high) {
            return;
        }
        p = a[low];
        i = low;
        j = high;
        while (i < j) {
            while (a[j] >= p && i < j) {
                j--;
            }
            while (a[i] <= p && i < j) {
                i++;
            }
            tmp = a[j];
            a[j] = a[i];
            a[i] = tmp;
        }
        a[low] = a[i];
        a[i] = p;
        sort(a, low, j - 1);
        sort(a, j + 1, high);
    }

    @Override
    protected Integer evalNExp(NExp exp, Env env) {
        if (exp instanceof Nat) {
            return evalNat((Nat) exp, env);
        }
        else if (exp instanceof SalesForM){
            return evalSalesForM(M);
        }
        else if(exp instanceof BinaryNExp){
            return evalBinaryNExp((BinaryNExp) exp, env);
        }
        else if(exp instanceof SalesAt){
            return evalSalesAt((SalesAt) exp, env);
        }
        else if(exp instanceof SalesForD){
            return evalSalesForD((SalesForD) exp, env);
        }
        else if(exp instanceof SalesForP){
            return evalSalesForP((SalesForP) exp, env);
        }
        else if(exp instanceof Var){
            return evalVar((Var) exp, env);
        }
        else if(exp instanceof Size){
            return evalSize((Size) exp, env);
        }
        return 0;
    }

    @Override
    protected Set<Integer> evalSExp(SExp exp, Env env)  {
        if (exp instanceof Type) {
            return evalType((Type) exp, env);
        }
        else if(exp instanceof BinarySExp){
            return evalBinarySExp((BinarySExp) exp, env);
        }
        else if(exp instanceof SetCompr){
            return evalSetCompr((SetCompr) exp, env);
        }
        return null;
    }

    @Override
    protected Boolean evalFormula(Formula formula, Env env) {
        if (formula instanceof Atomic) {
            return evalAtomic((Atomic) formula, env);
        }
        else if(formula instanceof Binary){
            return evalBinary((Binary) formula, env);
        }
        else if(formula instanceof Unary) {
            return evalUnary((Unary) formula, env);
        }
        else if(formula instanceof Quantified){
            return evalQuantified((Quantified) formula, env);
        }
        return false;
    }

    protected Integer evalVar(Var var, Env env) throws UnboundVariableException{
        if (env.lookup(var.name) == -1){
            throw new UnboundVariableException();
        }
        return env.lookup(var.name);
    }

    protected Integer evalSize(Size size, Env env){
        return evalSExp(size.sExp, env).size();
    }

    protected Integer evalBinaryNExp(BinaryNExp binaryNExp, Env env) throws DivisionByZeroException{
        if (binaryNExp.op.kind == BinNOp.Kind.ADD){
            return evalNExp(binaryNExp.lhs, env) + evalNExp(binaryNExp.rhs, env);
        }
        else if (binaryNExp.op.kind == BinNOp.Kind.DIFF){
            return evalNExp(binaryNExp.lhs, env) - evalNExp(binaryNExp.rhs, env);
        }
        else if (binaryNExp.op.kind == BinNOp.Kind.MULT){
            return evalNExp(binaryNExp.lhs, env) * evalNExp(binaryNExp.rhs, env);
        }
        else if (binaryNExp.op.kind == BinNOp.Kind.DIV){
            if (evalNExp(binaryNExp.rhs, env) == 0){
                throw new DivisionByZeroException();
            } else return evalNExp(binaryNExp.lhs, env) / evalNExp(binaryNExp.rhs, env);
            }
        else return null;
    }

    protected Integer evalSalesAt(SalesAt salesAt, Env env){
        return M[evalNExp(salesAt.product, env) - 1][evalNExp(salesAt.day, env) - 1];
    }

    protected Integer evalSalesForD(SalesForD salesForD, Env env){
        int sum = 0;
        int day = evalNExp(salesForD.day, env) - 1;
        for (int[] ints : M) {
            for (int j = 0; j < M[1].length; j++) {
                if (j == day) {
                    sum += ints[j];
                }
            }
        }
        return sum;
    }

    protected Integer evalSalesForP(SalesForP salesForP, Env env){
        int sum = 0;
        int prod = evalNExp(salesForP.product, env) - 1;
        for (int i = 0; i < M[prod].length; i++){
          sum += M[prod][i];
        }
        return sum;
    }

    protected Integer evalNat(Nat exp, Env env) {
        return exp.value;
    }

    protected Integer evalSalesForM(int[][] M){
        int sum = 0;
        for (int[] ints : M) {
            for (int j = 0; j < M[1].length; j++) {
                sum += ints[j];
            }
        }
        return sum;
    }

    protected Boolean evalAtomic(Atomic atomic, Env env) {
        if (atomic instanceof AtomicN) {
            return evalAtomicN((AtomicN) atomic, env);
        } else if (atomic instanceof AtomicS) {
            return evalAtomicS((AtomicS) atomic, env);
        }
        return false;
    }

    protected  Boolean evalBinary(Binary binary, Env env){
        if (binary.binConn.kind == BinaryConn.Kind.AND){
            return evalFormula(binary.lhs, env) && evalFormula(binary.rhs, env);
        }
        else if(binary.binConn.kind == BinaryConn.Kind.EQUIV){
            return (evalFormula(binary.lhs, env) == evalFormula(binary.rhs, env));
        }
        else if(binary.binConn.kind == BinaryConn.Kind.OR){
            return evalFormula(binary.lhs, env) || evalFormula(binary.rhs, env);
        }
        else if(binary.binConn.kind == BinaryConn.Kind.IMPLY){
            return !evalFormula(binary.lhs, env) || evalFormula(binary.rhs, env);
        }
        else return false;
    }

    protected Boolean evalUnary(Unary unary, Env env){
        return !evalFormula(unary.formula, env);
    }

    protected Boolean evalAtomicN(AtomicN atomicN, Env env) {
        int lhs = evalNExp(atomicN.lhs, env);
        int rhs = evalNExp(atomicN.rhs, env);
        if (lhs > rhs) {
            if (atomicN.relNOp.kind == RelNOp.Kind.GT || atomicN.relNOp.kind == RelNOp.Kind.NEQ) {
                return true;
            } else return atomicN.relNOp.kind == RelNOp.Kind.GTE;
        } else if (rhs == lhs) {
            if (atomicN.relNOp.kind == RelNOp.Kind.EQ) {
                return true;
            } else if (atomicN.relNOp.kind == RelNOp.Kind.GTE) {
                return true;
            } else return atomicN.relNOp.kind == RelNOp.Kind.LTE;
        } else {
            if (atomicN.relNOp.kind == RelNOp.Kind.LT || atomicN.relNOp.kind == RelNOp.Kind.NEQ ) {
                return true;
            } else return atomicN.relNOp.kind == RelNOp.Kind.LTE;
        }
    }

    protected Boolean evalQuantified(Quantified quantified, Env env){
        if (quantified.quantifier.kind == Quantifier.Kind.FORALL){
            boolean rst = true;
            for (Integer Int: evalSExp(quantified.type, env)){
                env.push(quantified.var.name, Int);
                rst = rst && evalFormula(quantified.formula, env);
                env.pop();
            }
            return rst;
        }else if(quantified.quantifier.kind == Quantifier.Kind.EXISTS) {
            boolean rst = false;
            for (Integer Int: evalSExp(quantified.type, env)){
                env.push(quantified.var.name, Int);
                rst = rst || evalFormula(quantified.formula, env);
                env.pop();
            }
            return rst;
        }
        else throw new UnboundVariableException();
    }

    protected Set<Integer> evalType(Type type, Env env)  {
        if (type.kind == Type.Kind.DAY) {
            int i = M[1].length;
            int j = 0;
            Set<Integer> st = new HashSet<>();
            while (i > 0) {
                st.add(j + 1);
                i--;
                j++;
            }
            return st;
        } else if (type.kind == Type.Kind.PRODUCT) {
            int i = M.length;
            int j = 0;
            Set<Integer> st = new HashSet<Integer>();
            while (i > 0) {
                st.add(j + 1);
                i--;
                j++;
            }
            return st;
        } else if (type.kind == Type.Kind.SALE) {
            Set<Integer> st = new HashSet<Integer>();
            int[] tmp = new int[M.length*M[1].length];
            int l = tmp.length - 1;
            int m = 0;
            for (int[] ints : M) {
                for (int j = 0; j < M[1].length; j++) {
                    tmp[m] = ints[j];
                    m++;
                }
            }
            sort(tmp, 0, l);
            for (int s = 0; s <= l; s++) {
                st.add(tmp[s]);
            }
            return st;
        }
        return null;
    }

    protected Set<Integer> evalBinarySExp(BinarySExp binarySExp, Env env) {
        Set<Integer> lhs = evalSExp(binarySExp.lhs, env);
        Set<Integer> rhs = evalSExp(binarySExp.rhs, env);
        if (binarySExp.op.kind == BinSOp.Kind.UNION){
            rhs.addAll(lhs);
            return rhs;
        }
        else if(binarySExp.op.kind == BinSOp.Kind.INTER){
            lhs.retainAll(rhs);
            return lhs;
        }
        else if(binarySExp.op.kind == BinSOp.Kind.DIFF){
            lhs.removeAll(rhs);
            return lhs;
        }
        else return null;
    }

    protected Set<Integer> evalSetCompr(SetCompr setCompr, Env env){
        Set<Integer> r = new HashSet<Integer>();
        for (Integer Int: evalSExp(setCompr.type, env)){
            env.push(setCompr.var.name, Int);
            if (evalFormula(setCompr.formula, env)){
                r.add(Int);
            }
        }
        return r;
    }

    protected Boolean evalAtomicS(AtomicS atomicS, Env env) {
        Set<Integer> lhs = evalSExp(atomicS.lhs, env);
        Set<Integer> rhs = evalSExp(atomicS.rhs, env);
        if (lhs.equals(rhs)) {
            return atomicS.relSOp.kind == RelSOp.Kind.EQ;
        } else {
            return atomicS.relSOp.kind != RelSOp.Kind.EQ;
        }
    }
}



