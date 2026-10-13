
/*
AllStraightLineAutGroups
Authors: Saul D. Freedman and Melissa Lee

Given an undirected graph G, this Magma function can be used to either:
1) calculate Aut(G)-conjugacy classes for the non-trivial elements and dihedral subgroups of Aut(G) that can be realized as symmetries or dihedral groups of symmetries of straight line drawings of G in the plane; or
2) determine whether at least one such element exists, i.e., if any straight line drawing of G in the plane has a non-trivial geometric symmetry that does not fix all vertices of G.

Usage: AllStraightLineAutGroups(G: Existence := ex, AutKnown := known, AutGp := autgp, Alg := alg);
	   
Arguments: G - the graph G.

Parameters: ex - false to execute algorithm 1) above, true to execute algorithm 2) (false by default).
			known - true if the user will provide the automorphism group of G, false otherwise (false by default).
			autgp - the automorphism group of G (only relevant if known is true; set to the trivial group by default).
			alg - the algorithm to be used to calculate the automorphism group of G (if known is false or no automorphism group is provided), either "nauty" or "Traces" ("nauty" by default).
				  Note: as of Magma V2.29-10, the Traces algorithm may not function correctly for certain graphs.
			
Returns: If ex is false, return a record rec where:
			rec`semiregs is a sequence of generators of cyclic subgroups realizable as rotations with no fixed vertices;
			rec`quasisemiregs is a sequence of generators of cyclic subgroups realizable as rotations with one fixed vertex;
			rec`reflections is a sequence of involutions realizable as reflections;
			rec`nofixeddihedrals is a sequence of realizable dihedral subgroups such that no vertex is fixed by all automorphisms; and
			rec`onefixeddihedrals is a sequence of realizable dihedral subgroups such that a common vertex is fixed by all automorphisms.
		 
         If ex is true, return true if a straight line drawing of G in the plane has a non-trivial geometric symmetry (that does not fix all vertices of G), false otherwise.

Last updated: October 13 2026.
*/
			
AllStraightLineAutGroups := function(G: Existence := false, AutKnown := false, AutGp := SymmetricGroup(1), Alg := "nauty")

	error if not ([Type(i):i in <G, Existence, AutKnown, AutGp>] eq [GrphUnd, BoolElt, BoolElt, GrpPerm] and Alg in ["nauty","Traces"]),\
	"Invalid argument/parameters; please see instructions.";

	//Compute the automorphism group if not provided - may be slow.

	if not AutKnown then
		aut, vset, eset := AutomorphismGroup(G: Al := Alg);
	else
		aut := AutGp;
		vset := Vertices(G);
		eset := Edges(G);
	end if;

	ccs := ConjugacyClasses(aut);
	
	if not Existence then
		semiregs := [];
		quasisemiregs := [];
		reflections := [];
	end if;
	
	for c in ccs do
		
		// Any (quasi-)semiregular element powers to a (quasi-)semiregular element of prime order, so if
		// we are only testing for existence of a geometric symmetry, it suffices to just check those.
		
		if Existence and not IsPrime(c[1]) then
			continue;
		end if;
		
		cyc := CycleStructure(c[3]);
		
		// Case 1: semiregular rotations and reflections
		if #cyc eq 1 and cyc[1][1] gt 1 then
		
			if Existence then
				return true;
			end if;
			
			Append(~semiregs, c[3]);
			
			// Each semiregular involution can be realized as a reflection
			if c[1] eq 2 then
				Append(~reflections, c[3]);
			end if;
			
		// Case 2: quasi-semiregular rotations and reflections
		elif #cyc eq 2 and <1,1> in cyc then
		
			if c[1] mod 2 eq 1 then
				
				if Existence then
					return true;
				end if;
			
				Append(~quasisemiregs, c[3]);
				
			else
			
				halforder := Integers()!(c[1]/2);
				new := c[3]^halforder;
				if #Fix(new,eset) eq 0 then
				
					if Existence then
						return true;
					end if;
				
					Append(~quasisemiregs, c[3]);
					
				end if;
				
			end if;
			
			// Each quasi-semiregular involution can be realized as a reflection
			if not Existence and c[1] eq 2 then
				Append(~reflections, c[3]);
			end if;
			
		// Case 3: reflections (that are neither semiregular nor quasi-semiregular)
		elif c[1] eq 2 then
		
			fixv := {vset!t:t in Fix(c[3])};
			
			// If the involution fixes at most 2 vertices, then we automatically know that it can be realized as a reflection.
			if #fixv le 2 then
			
				if Existence then
					return true;
				end if;
			
				Append(~reflections, c[3]);
			else
				indsub := sub<G | fixv>;
			
				compverts := Components(indsub);
				if forall{c:c in compverts | IsPath(Component(Rep(c)))} then
				
					if Existence then
						return true;
					end if;
					
					Append(~reflections, c[3]);
				
				end if;
					
			end if;
			
		end if;
		
	end for;
	
	// If no geometric symmetries have been found, then none exist.
	if Existence then
		return false;
	end if;
	
	//It remains to consider the dihedral groups, which are each generated by a rotation and a reflection inverting that rotation.
	
	dihedralgps:=[];
	Kleinfours:=[];
	cycsubdone:=[];
	
	// The following procedure finds the dihedral groups containing a given rotation i.
	
	StraightLineDihedralGroups := procedure(i,~dihedralgps,~Kleinfours,~cycsubdone)
	
		dihedralgps:=[];
	
		// Check if i is conjugate to its inverse.
		if Order(i) ne 2 and not IsConjugate(aut, i, i^-1) then
			return;
		end if;
		
		cycsub:=sub<aut | i>;
		
		// If the order of i is at least 5 (and not 6), there may be an element j in <i> with <i> = <j>, with j
		// not the inverse of i nor an Aut(G)-conjugate of i. We ensure that <i> is accounted for once up to
		// conjugacy, so that no dihedral subgroup of Aut(G) is returned twice (again up to conjugacy).
		if Order(i) ge 5 and Order(i) ne 6 then
			if exists{donesub:donesub in cycsubdone | IsConjugate(aut, donesub, cycsub)} then
				return;
			else
				Append(~cycsubdone,cycsub);
			end if;
		end if;
		
		n := Normalizer(aut, cycsub);
		nccs := Classes(n);
		// If g and x are elements of n with g inverting i, then the dihedral group <i, g> is
		// n-conjugate to <i^x, g^x>. Since i is a power of i^x, the latter group is equal to <i, g^x>.
		invclasses := [c:c in nccs | c[1] eq 2 and i^c[3] eq i^-1 and c[3] ne i];
		
		for c in invclasses do
		
			// Check if the involution c[3] is realizable as a reflection and, if |i| is even, if i*c[3] is also realizable as a reflection.
			
			if exists{r:r in reflections | IsConjugate(aut, r, c[3])} and (IsOdd(Order(i)) or exists{r:r in reflections | IsConjugate(aut, r, i*c[3])}) then
				dihedral := sub<aut | i, c[3]>;
				
				// Check if a conjugate of the current dihedral group has already been constructed. Extra care
				// must be taken if i has order 2, as i might also be realizable as a reflection.
				
				if Order(i) eq 2 then
					if not exists{d:d in Kleinfours | IsConjugate(aut, d, dihedral)} then
						Append(~Kleinfours, dihedral);
						Append(~dihedralgps, dihedral);
					end if;
				
				elif not exists{d:d in dihedralgps | IsConjugate(aut, d, dihedral)} then
					Append(~dihedralgps, dihedral);
				end if;
			end if;
		
		end for;
		
	end procedure;
	
	nofixeddihedrals := [];
	onefixeddihedrals := [];
	
	for i in semiregs do
	
		StraightLineDihedralGroups(i,~dihedralgps,~Kleinfours,~cycsubdone);
		nofixeddihedrals := nofixeddihedrals cat dihedralgps;
	
	end for;
	
	for i in quasisemiregs do
		
		StraightLineDihedralGroups(i,~dihedralgps,~Kleinfours,~cycsubdone);
		onefixeddihedrals := onefixeddihedrals cat dihedralgps;
	
	end for;
	
	RF := recformat<semiregs, quasisemiregs, reflections, nofixeddihedrals, onefixeddihedrals>;
	
	return rec<RF | semiregs := semiregs, quasisemiregs := quasisemiregs, reflections := reflections, nofixeddihedrals := nofixeddihedrals, onefixeddihedrals := onefixeddihedrals>;

end function;
