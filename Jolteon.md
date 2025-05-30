# Decidability of logical propositions

All the logical propositional appearing in the formulation
of the Jolteon protocol (c.f. `Jolteon`) are in fact **decidable**,
meaning that we can utilize *proof-by-computation* to automatically discharge
proofs on closed terms. (c.f. `Jolteon.Test`).

Many of these are **already** decidable, by virtue of the decidability of their
building blocks.

The rest of these files provide manual proofs that this is indeed the case
for all other propositions where this is not automatically derived.

<pre class="Agda"><a id="544" class="Symbol">{-#</a> <a id="548" class="Keyword">OPTIONS</a> <a id="556" class="Pragma">--safe</a> <a id="563" class="Symbol">#-}</a>
<a id="567" class="Keyword">open</a> <a id="572" class="Keyword">import</a> <a id="579" href="Jolteon.Assumptions.html" class="Module">Jolteon.Assumptions</a>

<a id="600" class="Keyword">module</a> <a id="607" href="Jolteon.html" class="Module">Jolteon</a> <a id="615" class="Symbol">(</a><a id="616" href="Jolteon.html#616" class="Bound">⋯</a> <a id="618" class="Symbol">:</a> <a id="620" href="Jolteon.Assumptions.html#193" class="Record">Assumptions</a><a id="631" class="Symbol">)</a> <a id="633" class="Keyword">where</a>

<a id="640" class="Keyword">open</a> <a id="645" class="Keyword">import</a> <a id="652" href="Jolteon.Base.html" class="Module">Jolteon.Base</a> <a id="665" class="Keyword">public</a>
<a id="672" class="Keyword">open</a> <a id="677" class="Keyword">import</a> <a id="684" href="Jolteon.Assumptions.html" class="Module">Jolteon.Assumptions</a> <a id="704" class="Keyword">public</a>

<a id="712" class="Keyword">open</a> <a id="717" class="Keyword">import</a> <a id="724" href="Jolteon.Block.html" class="Module">Jolteon.Block</a> <a id="738" href="Jolteon.html#616" class="Bound">⋯</a> <a id="740" class="Keyword">public</a>
<a id="747" class="Keyword">open</a> <a id="752" class="Keyword">import</a> <a id="759" href="Jolteon.Message.html" class="Module">Jolteon.Message</a> <a id="775" href="Jolteon.html#616" class="Bound">⋯</a> <a id="777" class="Keyword">public</a>
<a id="784" class="Keyword">open</a> <a id="789" class="Keyword">import</a> <a id="796" href="Jolteon.Local.State.html" class="Module">Jolteon.Local.State</a> <a id="816" href="Jolteon.html#616" class="Bound">⋯</a> <a id="818" class="Keyword">public</a>
<a id="825" class="Keyword">open</a> <a id="830" class="Keyword">import</a> <a id="837" href="Jolteon.Local.Step.html" class="Module">Jolteon.Local.Step</a> <a id="856" href="Jolteon.html#616" class="Bound">⋯</a> <a id="858" class="Keyword">public</a>
<a id="865" class="Keyword">open</a> <a id="870" class="Keyword">import</a> <a id="877" href="Jolteon.Global.State.html" class="Module">Jolteon.Global.State</a> <a id="898" href="Jolteon.html#616" class="Bound">⋯</a> <a id="900" class="Keyword">public</a>
<a id="907" class="Keyword">open</a> <a id="912" class="Keyword">import</a> <a id="919" href="Jolteon.Global.NoForging.html" class="Module">Jolteon.Global.NoForging</a> <a id="944" href="Jolteon.html#616" class="Bound">⋯</a> <a id="946" class="Keyword">public</a>
  <a id="955" class="Keyword">using</a> <a id="961" class="Symbol">(</a><a id="962" href="Jolteon.Global.NoForging.html#2014" class="Function">NoSignatureForging</a><a id="980" class="Symbol">)</a>
<a id="982" class="Keyword">open</a> <a id="987" class="Keyword">import</a> <a id="994" href="Jolteon.Global.Step.html" class="Module">Jolteon.Global.Step</a> <a id="1014" href="Jolteon.html#616" class="Bound">⋯</a> <a id="1016" class="Keyword">public</a>
<a id="1023" class="Keyword">open</a> <a id="1028" class="Keyword">import</a> <a id="1035" href="Jolteon.Global.Trace.html" class="Module">Jolteon.Global.Trace</a> <a id="1056" href="Jolteon.html#616" class="Bound">⋯</a> <a id="1058" class="Keyword">public</a>
</pre>