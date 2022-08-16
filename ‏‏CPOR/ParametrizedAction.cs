using System.Collections.Generic;

namespace CPOR
{
    class ParametrizedAction : Action
    {
        public List<Parameter> Parameters { get; private set; }
        public ParametrizedAction(string sName)
            : base(sName)
        {
            Parameters = new List<Parameter>();
            ParameterNameToType = new Dictionary<string, string>();
        }
        public Dictionary<string, string> ParameterNameToType { get; private set; }
        public void AddParameter(Parameter parameter)
        {
            Parameters.Add(parameter);
            ParameterNameToType[parameter.Name] = parameter.Type;
        }
        public override Action Clone()
        {
            ParametrizedAction aNew = new ParametrizedAction(Name);
            aNew.Parameters = Parameters;
            if (Preconditions != null)
                aNew.Preconditions = Preconditions.Clone();
            if (Effects != null)
                aNew.SetEffects(Effects.Clone());
            if (Observe != null)
                aNew.Observe = Observe.Clone();
            aNew.HasConditionalEffects = HasConditionalEffects;
            aNew.ContainsNonDeterministicEffect = ContainsNonDeterministicEffect;
            return aNew;
        }

        public override string ToString()
        {
            string s = "(:action " + Name + "\n";
            s += " :parameters (";
            foreach (Parameter p in Parameters)
            {
                s += p.Name + " - " + p.Type + " ";
            }
            s += ")\n";
            if (Preconditions != null)
                s += " :precondition " + Preconditions + "\n";
            if (Effects != null)
                s += " :effect " + Effects + "\n";
            if (Observe != null)
                s += " :observe " + Observe + "\n";
            s += ")";
            return s;
        }

    }
}
