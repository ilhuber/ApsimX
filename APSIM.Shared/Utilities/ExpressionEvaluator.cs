using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Text.RegularExpressions;

namespace APSIM.Shared.Utilities
{
    /// <summary>
    ///
    /// </summary>
    public enum ExpressionType
    {
        /// <summary>The variable</summary>
        Variable,

        /// <summary>The value</summary>
        Value,

        /// <summary>The operator</summary>
        Operator,

        /// <summary>The eval function</summary>
        EvalFunction,

        /// <summary>The result</summary>
        Result,

        /// <summary>A left bracket</summary>
        LeftBracket,

        /// <summary>A right bracket</summary>
        RightBracket,

        /// <summary>The comma</summary>
        Comma,

        /// <summary>The error</summary>
        Error
    }
    /// <summary>
    ///
    /// </summary>
    [Serializable]
    public struct Symbol
    {
        /// <summary>The m_name</summary>
        public string m_name;
        /// <summary>The m_value</summary>
        public double m_value;
        /// <summary>The m_values</summary>
        public double[] m_values;
        /// <summary>The m_type</summary>
        public ExpressionType m_type;
        /// <summary>Returns a <see cref="System.String" /> that represents this instance.</summary>
        /// <returns>A <see cref="System.String" /> that represents this instance.</returns>
        public override string ToString()
        {
            return m_name;
        }
    }
    /// <summary>
    ///
    /// </summary>
    /// <param name="name">The name.</param>
    /// <param name="args">The arguments.</param>
    /// <returns></returns>
    public delegate Symbol EvaluateFunctionDelegate(string name, params Object[] args);
    ///<author>Emad Barsoum</author>
    ///<email>ebarsoum@msn.com</email>
    ///<date>March 23, 2002</date>
    ///<copyright>
    ///This code is Copyright to Emad Barsoum, it can be used or changed for free without removing the header
    ///information which is the author name, email and date or refer to this information if any change made.
    ///</copyright>
    ///<summary>
    ///This class <c>EvalFunction</c> use the transformation from infix notation to postfix notation to evalute most
    ///Mathematic expression, it support most operators (+,-,*,/,%,^), functions from 0 to any number of parameters
    ///and also a user defined function by using delegate, also it support variables in the expression, it will
    ///generate a symbol table that can be updated at run time.
    ///</summary>
    [Serializable]
    public class ExpressionEvaluator
    {
        /// <summary>Gets the result.</summary>
        /// <value>The result.</value>
        public double Result
        {
            get
            {
                return m_result;
            }
        }

        /// <summary>Gets the results.</summary>
        /// <value>The results.</value>
        public double[] Results
        {
            get
            {
                return m_results;
            }
        }

        /// <summary>Gets the equation.</summary>
        /// <value>The equation.</value>
        public List<Symbol> Equation
        {
            get
            {
                return new List<Symbol>(m_equation);
            }
        }
        /// <summary>Gets the postfix.</summary>
        /// <value>The postfix.</value>
        public List<Symbol> Postfix
        {
            get
            {
                return new List<Symbol>(m_postfix);
            }
        }

        /// <summary>Sets the default function evaluation.</summary>
        /// <value>The default function evaluation.</value>
        public EvaluateFunctionDelegate DefaultFunctionEvaluation
        {
            set
            {
                m_defaultFunctionEvaluation = value;
            }
        }

        /// <summary>Gets a value indicating whether this <see cref="ExpressionEvaluator"/> is error.</summary>
        /// <value><c>true</c> if error; otherwise, <c>false</c>.</value>
        public bool Error
        {
            get
            {
                return m_bError;
            }
        }

        /// <summary>Gets the error description.</summary>
        /// <value>The error description.</value>
        public string ErrorDescription
        {
            get
            {
                return m_sErrorDescription;
            }
        }

        /// <summary>Gets or sets the variables.</summary>
        /// <value>The variables.</value>
        public List<Symbol> Variables
        {
            get => _variables;
            set
            {
                foreach (Symbol sym in value)
                    foreach (var idx in _variableIndexMap[sym.m_name])
                        m_postfix[idx] = sym;
            }
        }

        /// <summary>A list of the variables associated with this expression.</summary>
        private List<Symbol> _variables = new();

        /// <summary>A mapping of variable name to each occurence in the postfix equation.</summary>
        private Dictionary<string, List<int>> _variableIndexMap = new();

        /// <summary>Initializes a new instance of the <see cref="ExpressionEvaluator"/> class.</summary>
        public ExpressionEvaluator()
        { }

        /// <summary>Parses the specified equation.</summary>
        /// <param name="equation">The equation.</param>
        public void Parse(string equation)
        {
            // Tracks the nesting depth of brackets. Brackets are unmatched if ever negative or nonzero at the end of the iteration.
            var bracketTracker = 0;
            Symbol ctSymbol = new Symbol();
            ctSymbol.m_values = null;

            m_bError = false;
            m_sErrorDescription = "None";

            m_equation.Clear();
            _variables.Clear();
            m_postfix.Clear();
            _variableIndexMap.Clear();

            //-- Remove all white spaces from the equation string --
            var matches = s_parseRegex.Matches(equation.Replace(" ", ""));
            foreach (Match m in matches)
            {
                ctSymbol.m_name = m.Value;
                // Awkward. Get the first named group this matches.
                var g = m.Groups.Cast<Group>()
                    .Where(g => g.Success && g.Name.All(c => !char.IsNumber(c)))
                    .First();
                switch (g.Name)
                {
                    case "evalfn":
                        ctSymbol.m_type = ExpressionType.EvalFunction;
                        break;
                    case "variable":
                        ctSymbol.m_type = ExpressionType.Variable;
                        if (m.Value == "pi")
                            ctSymbol.m_value = Math.PI;
                        else if (m.Value == "e")
                            ctSymbol.m_value = Math.E;
                        break;
                    case "value":
                        ctSymbol.m_type = ExpressionType.Value;
                        ctSymbol.m_value = Convert.ToDouble(m.Value, CultureInfo.InvariantCulture);
                        break;
                    case "comma":
                        ctSymbol.m_type = ExpressionType.Comma;
                        break;
                    case "lbracket":
                        ++bracketTracker;
                        ctSymbol.m_type = ExpressionType.LeftBracket;
                        break;
                    case "rbracket":
                        --bracketTracker;
                        ctSymbol.m_type = ExpressionType.RightBracket;
                        break;
                    case "operator":
                    default:
                        ctSymbol.m_type = ExpressionType.Operator;
                        if (m.Value == "-" && CheckUnaryMinus())
                            // Use -- to indicate unary minus
                            ctSymbol.m_name = "--";
                        break;
                }
                if (bracketTracker < 0)
                    throw new ArgumentException($"Unmatched right parenthesis in {equation}!");
                m_equation.Add(ctSymbol);
                if (ctSymbol.m_type == ExpressionType.Variable)
                    _variables.Add(ctSymbol);
            }
            if (bracketTracker != 0)
                throw new ArgumentException($"Unmatched left parethesis in {equation}!");
            // A minus sign is always unary if it immediately follows another operator or left parenthesis.
            bool CheckUnaryMinus() =>
                m_equation.Count < 1 ||
                m_equation.Last().m_type == ExpressionType.Operator ||
                m_equation.Last().m_type == ExpressionType.LeftBracket;
        }

        /// <summary>Parses lexed tokens into postfix notation thunk.</summary>
        public void Infix2Postfix()
        {
            Stack<Symbol> stack = new Stack<Symbol>();
            foreach(var sym in m_equation)
            {
                if ((sym.m_type == ExpressionType.Value) || (sym.m_type == ExpressionType.Variable))
                    m_postfix.Add(sym);
                else if (sym.m_type == ExpressionType.LeftBracket)
                    stack.Push(sym);
                else if (sym.m_type == ExpressionType.RightBracket)
                {
                    while (stack.Count > 0)
                    {
                        var topSym = stack.Pop();
                        if (topSym.m_type == ExpressionType.LeftBracket)
                            break;
                        m_postfix.Add(topSym);
                    }
                }
                else
                {
                    while (stack.Count > 0)
                    {
                        // Pop away higher precedence symbols.
                        var topSym = stack.Peek();
                        if (((topSym.m_type == ExpressionType.Operator) || (topSym.m_type == ExpressionType.EvalFunction) || (topSym.m_type == ExpressionType.Comma)) && (Precedence(topSym) >= Precedence(sym)))
                            m_postfix.Add(stack.Pop());
                        else
                            break;
                    }
                    stack.Push(sym);
                }
            }
            while (stack.Count > 0)
                m_postfix.Add(stack.Pop());
            for (int i = 0; i < m_postfix.Count; i++)
            {
                var sym = m_postfix[i];
                if (m_postfix[i].m_type == ExpressionType.Variable)
                    if (_variableIndexMap.ContainsKey(sym.m_name))
                        _variableIndexMap[sym.m_name].Add(i);
                    else
                        _variableIndexMap.Add(sym.m_name, new List<int> { i });
            }
        }

        /// <summary>Evaluates the postfix.</summary>
        public void EvaluatePostfix()
        {
            Symbol tpSym1, tpSym2, tpResult;
            Stack<Symbol> tpStack = new Stack<Symbol>();
            List<Symbol> fnParam = new List<Symbol>();
            m_bError = false;
            foreach (Symbol sym in m_postfix)
            {
                if ((sym.m_type == ExpressionType.Value) || (sym.m_type == ExpressionType.Variable) || (sym.m_type == ExpressionType.Result))
                    tpStack.Push(sym);
                else if (sym.m_type == ExpressionType.Operator)
                {
                    tpSym1 = (Symbol)tpStack.Pop();
                    if (tpStack.Count > 0 && sym.m_name != "--")
                        tpSym2 = tpStack.Pop();
                    else
                        tpSym2 = new Symbol();
                    tpResult = Evaluate(tpSym2, sym, tpSym1);
                    if (tpResult.m_type == ExpressionType.Error)
                    {
                        m_bError = true;
                        m_sErrorDescription = tpResult.m_name;
                        return;
                    }
                    tpStack.Push(tpResult);
                }
                else if (sym.m_type == ExpressionType.Comma)
                    // Commas need to be added onto the parameter stack, otherwise
                    // only the last argument will be passed to the function call.
                    tpStack.Push(sym);
                else if (sym.m_type == ExpressionType.EvalFunction)
                {
                    fnParam.Clear();
                    tpSym1 = tpStack.Pop();
                    if ((tpSym1.m_type == ExpressionType.Value) || (tpSym1.m_type == ExpressionType.Variable) || (tpSym1.m_type == ExpressionType.Result))
                    {
                        tpResult = EvaluateFunction(sym.m_name, tpSym1);
                        if (tpResult.m_type == ExpressionType.Error)
                        {
                            m_bError = true;
                            m_sErrorDescription = tpResult.m_name;
                            return;
                        }
                        tpStack.Push(tpResult);
                    }
                    else if (tpSym1.m_type == ExpressionType.Comma)
                    {
                        while (tpSym1.m_type == ExpressionType.Comma)
                        {
                            tpSym1 = tpStack.Pop();
                            // tpStack is postfix order, however EvaluateFunction() expects the parameter
                            // array to be in prefix order, so fnParam is prefix order.
                            fnParam.Insert(0, tpSym1);
                            tpSym1 = tpStack.Pop();
                        }
                        fnParam.Insert(0, tpSym1);
                        tpResult = EvaluateFunction(sym.m_name, fnParam.ToArray());
                        if (tpResult.m_type == ExpressionType.Error)
                        {
                            m_bError = true;
                            m_sErrorDescription = tpResult.m_name;
                            return;
                        }
                        tpStack.Push(tpResult);
                    }
                    else
                    {
                        tpStack.Push(tpSym1);
                        tpResult = EvaluateFunction(sym.m_name);
                        if (tpResult.m_type == ExpressionType.Error)
                        {
                            m_bError = true;
                            m_sErrorDescription = tpResult.m_name;
                            return;
                        }
                        tpStack.Push(tpResult);
                    }
                }
            }
            if (tpStack.Count == 1)
            {
                tpResult = tpStack.Pop();
                m_result = tpResult.m_value;
                if (tpResult.m_values != null)
                {
                    m_results = tpResult.m_values;
                }
            }
        }

        /// <summary>Precedences the specified sym.</summary>
        /// <param name="sym">The sym.</param>
        /// <returns></returns>
        /// <remarks>
        /// I give unary minus a higher precedence than multiplication, division,
        /// and exponentiation. e.g.
        ///
        /// -2^4 = 16, not -16
        /// </remarks>
        protected int Precedence(Symbol sym)
        {
            switch (sym.m_type)
            {
                case ExpressionType.LeftBracket:
                case ExpressionType.RightBracket:
                    return 6;
                case ExpressionType.EvalFunction:
                    return 5;
                case ExpressionType.Comma:
                    return 0;
            }
            switch (sym.m_name)
            {
                case "--":
                    return 4;
                case "^":
                    return 3;
                case "/":
                case "*":
                case "%":
                    return 2;
                case "+":
                case "-":
                    return 1;
            }
            return -1;
        }

        /// <summary>Evaluates the specified sym1.</summary>
        /// <param name="sym1">The sym1.</param>
        /// <param name="opr">The opr.</param>
        /// <param name="sym2">The sym2.</param>
        /// <returns></returns>
        protected Symbol Evaluate(Symbol sym1, Symbol opr, Symbol sym2)
        {
            Symbol result;
            if (opr.m_name == "--")
                result.m_name = "-" + sym2.m_name;
            else
                result.m_name = sym1.m_name + opr.m_name + sym2.m_name;
            result.m_type = ExpressionType.Result;
            result.m_value = 0;
            result.m_values = null;
            switch (opr.m_name)
            {
                case "^":
                    EvaluateOperator(Math.Pow);
                    break;
                case "/":
                    if (sym2.m_values is null && MathUtilities.FloatsAreEqual(sym2.m_value, 0, 1E-12))
                    {
                        result.m_name = "Divide by Zero.";
                        result.m_type = ExpressionType.Error;
                    }
                    else
                        EvaluateOperator((l, r) => l / r);
                    break;
                case "*":
                    EvaluateOperator((l, r) => l * r);
                    break;
                case "%":
                    EvaluateOperator((l, r) => l % r);
                    break;
                case "+":
                    EvaluateOperator((l, r) => l + r);
                    break;
                case "-":
                    EvaluateOperator((l, r) => l - r);
                    break;
                case "--":
                    // Operand is on the right for unary minus.
                    EvaluateOperator((_, r) => -1 * r);
                    break;
                default:
                    result.m_type = ExpressionType.Error;
                    result.m_name = "Undefined operator: " + opr.m_name + ".";
                    break;
            }
            return result;

            void EvaluateOperator(Func<double, double, double> op)
            {
                if (sym1.m_values != null && sym2.m_values != null)
                    result.m_values = sym1.m_values.Zip(sym2.m_values, op).ToArray();
                else if (sym1.m_values != null)
                    result.m_values = sym1.m_values.Select(v => op(v, sym2.m_value)).ToArray();
                else if (sym2.m_values != null)
                    result.m_values = sym2.m_values.Select(v => op(sym1.m_value, v)).ToArray();
                else
                    result.m_value = op(sym1.m_value, sym2.m_value);
            }
        }

        /// <summary>Evaluates the function.</summary>
        /// <param name="name">The name.</param>
        /// <param name="args">The arguments (in prefix order - not postfix!).</param>
        /// <returns></returns>
        protected Symbol EvaluateFunction(string name, params Symbol[] args)
        {
            Symbol result;
            result.m_name = "";
            result.m_type = ExpressionType.Result;
            result.m_value = 0;
            result.m_values = null;
            switch (name.ToLower())
            {
                case "cos":
                    EvaluateUnaryFunction(Math.Cos);
                    break;
                case "sin":
                    EvaluateUnaryFunction(Math.Sin);
                    break;
                case "tan":
                    EvaluateUnaryFunction(Math.Tan);
                    break;
                case "cosh":
                    EvaluateUnaryFunction(Math.Cosh);
                    break;
                case "sinh":
                    EvaluateUnaryFunction(Math.Sinh);
                    break;
                case "tanh":
                    EvaluateUnaryFunction(Math.Tanh);
                    break;
                case "log10":
                    EvaluateUnaryFunction(Math.Log10);
                    break;
                case "ln":
                    EvaluateUnaryFunction(Math.Log);
                    break;
                case "logn":
                    if (args.Length != 2)
                    {
                        result.m_name = $"Invalid number of parameters in: {name}.";
                        result.m_type = ExpressionType.Error;
                        break;
                    }
                    if (args[1].m_values != null)
                    {
                        result.m_name = "logn function does not support vector of bases";
                        result.m_type = ExpressionType.Error;
                        break;
                    }
                    result.m_name = $"{name}({args[0].m_value.ToString()}'{args[1].m_value.ToString()})";
                    if (args[0].m_values == null)
                        result.m_value = Math.Log(args[0].m_value, args[1].m_value);
                    else
                        result.m_values = args[0].m_values.Select(v => Math.Log(v, args[1].m_value)).ToArray();
                    break;
                case "sqrt":
                    EvaluateUnaryFunction(Math.Sqrt);
                    break;
                case "abs":
                    EvaluateUnaryFunction(Math.Abs);
                    break;
                case "acos":
                    EvaluateUnaryFunction(Math.Acos);
                    break;
                case "asin":
                    EvaluateUnaryFunction(Math.Asin);
                    break;
                case "atan":
                    EvaluateUnaryFunction(Math.Atan);
                    break;
                case "exp":
                    EvaluateUnaryFunction(Math.Exp);
                    break;
                case "mean":
                    EvaluateVectorFunction(MathUtilities.Average);
                    break;
                case "sum":
                case "value":
                    EvaluateVectorFunction(MathUtilities.Sum);
                    break;
                case "subtract":
                    EvaluateVectorFunction(arr => arr.Aggregate((l, r) => l - r));
                    break;
                case "multiply":
                    EvaluateVectorFunction(MathUtilities.Prod);
                    break;
                case "divide":
                    if (args.Length == 2 || args.Length == 3)
                    {
                        // Iff 3 args provided, use 3rd arg as error value.
                        double errorValue = args.Length == 2 ? 0 : args[2].m_value;
                        result.m_name = name;
                        result.m_value = MathUtilities.Divide(args[0].m_value, args[1].m_value, errorValue);
                        break;
                    }
                    EvaluateVectorFunction(arr => arr.Aggregate((l, r) => MathUtilities.FloatsAreEqual(r, 0, 1e-8) ?  0 : l / r));
                    break;
                case "min":
                    EvaluateVectorFunction(MathUtilities.Min);
                    break;
                case "max":
                    EvaluateVectorFunction(MathUtilities.Max);
                    break;
                case "floor":
                    EvaluateUnaryFunction(Math.Floor);
                    break;
                case "ceil":
                case "ceiling":
                    EvaluateUnaryFunction(Math.Ceiling);
                    break;
                case "stddev":
                    EvaluateVectorFunction(MathUtilities.StandardDeviation);
                    break;
                case "percentile5":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.05));
                    break;
                case "percentile10":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.10));
                    break;
                case "percentile15":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.15));
                    break;
                case "percentile20":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.20));
                    break;
                case "percentile25":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.25));
                    break;
                case "percentile30":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.30));
                    break;
                case "percentile35":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.35));
                    break;
                case "percentile40":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.40));
                    break;
                case "percentile45":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.45));
                    break;
                case "median":
                case "percentile50":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.50));
                    break;
                case "percentile55":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.55));
                    break;
                case "percentile60":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.60));
                    break;
                case "percentile65":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.65));
                    break;
                case "percentile70":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.70));
                    break;
                case "percentile75":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.75));
                    break;
                case "percentile80":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.80));
                    break;
                case "percentile85":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.85));
                    break;
                case "percentile90":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.90));
                    break;
                case "percentile95":
                    EvaluateVectorFunction(arr => MathUtilities.Percentile(arr, 0.95));
                    break;
                default:
                    if (m_defaultFunctionEvaluation != null)
                        result = m_defaultFunctionEvaluation(name, args);
                    else
                    {
                        result.m_name = "EvalFunction: " + name + ", not found.";
                        result.m_type = ExpressionType.Error;
                    }
                    break;
            }
            return result;

            // Evaluates a single argument function, either by applying it to a single value, or
            // mapping across a vector of values.
            void EvaluateUnaryFunction(Func<double, double> fn)
            {
                if (args.Length != 1)
                {
                    result.m_name = "Invalid number of parameters in: " + name + ".";
                    result.m_type = ExpressionType.Error;
                    return;
                }
                result.m_name = $"{name}({args[0].m_value.ToString()})";
                if (args[0].m_values == null)
                    result.m_value = fn(args[0].m_value);
                else
                    result.m_values = args[0].m_values.Select(fn).ToArray();
            }

            // Evaluates a function intended to be used on a vector of values, like sum or stdev.
            void EvaluateVectorFunction(Func<double[], double> fn)
            {
                if (args.Length != 1)
                {
                    result.m_name = "Invalid number of parameters in: " + name + ".";
                    result.m_type = ExpressionType.Error;
                    return;
                }
                result.m_value = fn(args[0].m_values);
                result.m_name = name;
                result.m_values = null;
            }
        }

        /// <summary>Regular expression that defines the simple grammar used by the expression evaluator </summary>
        private static readonly Regex s_parseRegex =
            new(String.Join('|', new[] {
                // Characters followed by a not included opening brace not immediately closed.
                @"(?<evalfn>\w+(?=\([^\)]))",
                // A token consisting of at least one string beginning with a character
                // or '[' separated by '.' and possibly ending in ()
                @"(?<variable>([A-Za-z\[][A-Za-z0-9:_]*\]?\.?)+(\(\))?)",
                // Decimal numbers
                @"(?<value>\d+\.?\d*)",
                // Something from the operator set
                @"(?<operator>[+\-*/\^%])",
                // An opening parentheses or curly brace (apperently?)
                @"(?<lbracket>[\(\{])",
                // A closing parenthesis or curly brace
                @"(?<rbracket>)[\)\}]",
                // Just a comma
                @"(?<comma>,)"}));

        /// <summary>The M_B error</summary>
        protected bool m_bError = false;
        /// <summary>The M_S error description</summary>
        protected string m_sErrorDescription = "None";
        /// <summary>The m_result</summary>
        protected double m_result = 0;
        /// <summary>The m_results</summary>
        protected double[] m_results = null;
        /// <summary>The m_equation</summary>
        protected List<Symbol> m_equation = new List<Symbol>();
        /// <summary>The m_postfix</summary>
        protected List<Symbol> m_postfix = new List<Symbol>();
        /// <summary>The m_default function evaluation</summary>
        protected EvaluateFunctionDelegate m_defaultFunctionEvaluation;
    }
}
