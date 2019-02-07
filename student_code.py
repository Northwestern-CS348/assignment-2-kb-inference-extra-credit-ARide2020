import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_delete(self, fact_or_rule):
        if(len(fact_or_rule.supported_by) != 0):
            if(fact_or_rule.asserted):
                fact_or_rule.asserted = False
            return

        if isinstance(fact_or_rule, Fact) and fact_or_rule in self.facts:
            if(len(fact_or_rule.supports_facts) != 0):                
                for sf in fact_or_rule.supports_facts:
                    for pair in sf.supported_by:
                        if pair[0] == fact_or_rule:
                            sf.supported_by.remove(pair)
                    if(len(sf.supported_by) == 0) and not sf.asserted:
                        self.kb_delete(sf)
            if(len(fact_or_rule.supports_rules) != 0):            
                for sr in fact_or_rule.supports_rules:
                    for pair in sr.supported_by:
                        if pair[0] == fact_or_rule:
                            sr.supported_by.remove(pair)
                    if(len(sr.supported_by) == 0) and not sr.asserted:
                        self.kb_delete(sr)
            self.facts.remove(fact_or_rule)

        if isinstance(fact_or_rule, Rule) and fact_or_rule in self.rules:
            if(len(fact_or_rule.supports_facts) != 0):                
                for sf in fact_or_rule.supports_facts:
                    for pair in sf.supported_by:
                        if pair[1] == fact_or_rule:
                            sf.supported_by.remove(pair)
                    if(len(sf.supported_by) == 0) and not sf.asserted:
                        self.kb_delete(sf)
            if(len(fact_or_rule.supports_rules) != 0):            
                for sr in fact_or_rule.supports_rules:
                    for pair in sr.supported_by:
                        if pair[1] == fact_or_rule:
                            sr.supported_by.remove(pair)
                    if(len(sr.supported_by) == 0) and not sr.asserted:
                        self.kb_delete(sr)
            self.rules.remove(fact_or_rule)

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        if isinstance(fact_or_rule,Fact):
            if fact_or_rule in self.facts:
             self.kb_delete(self._get_fact(fact_or_rule))

    def kb_helps(self, fact_or_rule, ftorrl, num):
        if(ftorrl == 'r'):
            state = "("
            FactRule = self._get_rule(fact_or_rule)            

            if(len(FactRule.lhs) != 0):
                for s in FactRule.lhs:
                    state += str(s) + ", "
                state = state[:-1]
                state = state[:-1]

            state += ") -> " + str(FactRule.rhs)

        if(ftorrl == 'f'):
            FactRule = self._get_fact(fact_or_rule)
            state = str(FactRule.statement)

        result = " " * num + FactRule.name + ": " + state

        if(FactRule.asserted):
            result = result + " ASSERTED\n"
        else:
            result = result + "\n"

        for pairs in FactRule.supported_by:
            result = result + " " * (num + 2) + "SUPPORTED BY\n"
            result = result + self.kb_helps(pairs[0], 'f',num + 4) + self.kb_helps(pairs[1], 'r', num + 4)

        return result
    

    def kb_explain(self, fact_or_rule):
        """
        Explain where the fact or rule comes from

        Args:
            fact_or_rule (Fact or Rule) - Fact or rule to be explained

        Returns:
            string explaining hierarchical support from other Facts and rules
        """
        ###################################################
        if isinstance(fact_or_rule, Fact):
            if fact_or_rule in self.facts:
                return self.kb_helps(fact_or_rule, 'f', 0)
            else:
                return "Fact is not in the KB"
        elif isinstance(fact_or_rule, Rule):
            if fact_or_rule in self.rules:
                 return self.kb_helps(fact_or_rule, 'r', 0)
            else:
                return "Rule is not in the KB"
        else:
            return False


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Implementation goes here
        binds = match(rule.lhs[0], fact.statement)

        if binds != False:
            if (len(rule.lhs) == 1):
                newf = instantiate(rule.rhs,binds)

                f = Fact(newf,[[fact,rule]])

                kb.kb_add(f)

                f = kb._get_fact(f)

                rule.supports_facts.append(f)
                fact.supports_facts.append(f)
            else:
                #for rule there is more than one lhs so you have to instantiate all of them and the rhs
                lstofstants = []
                for l in rule.lhs[1:]:
                    lstofstants.append(instantiate(l,binds))
                
                #lstofstants.remove(lstofstants[0])

                rhstant = instantiate(rule.rhs, binds)
                
                newr = Rule([lstofstants,rhstant],[[fact,rule]])
                
                kb.kb_add(newr)

                r = kb._get_rule(newr)

                rule.supports_rules.append(r)
                fact.supports_rules.append(r)

