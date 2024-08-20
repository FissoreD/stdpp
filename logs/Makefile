plot11:
	python ../scripts/parse_elpi_stat.py stat_w_time_01.log stat_w_time_no_elpi_01.log 

plot21:
	python ../scripts/parse_elpi_stat.py stat_w_time_02.log stat_w_time_no_elpi_01.log 

plot31:
	python ../scripts/parse_elpi_stat.py stat_w_time_03.log stat_w_time_no_elpi_01.log 

plot51:
	python ../scripts/parse_elpi_stat.py stat_w_time_05.log stat_w_time_no_elpi_01.log 

plot61:
	python ../scripts/parse_elpi_stat.py stat_w_time_06.log stat_w_time_no_elpi_01.log 

plot_dis11:
	python ../scripts/parse_elpi_stat.py stat_w_time_01.log stat_w_time_elpi_disabled_01.log 

plot_dis12:
	python ../scripts/parse_elpi_stat.py stat_w_time_01.log stat_w_time_elpi_disabled_02.log 

# In this version I activate the mode for the class Lookup + add the rule
# Elpi Accumulate TC.Solver lp:{{
#   pred is-seal-mode i:sealed-goal, o:sealed-goal.
#   is-seal-mode (seal-mode S) S :- !.
#   is-seal-mode (seal G) (seal G) :- !.
#   is-seal-mode (nabla B) (nabla C) :- pi x\ is-seal-mode (B x) (C x).
# 
#   pred partition-clean-s-mode i:list A, o:list B, o:list A.
#   partition-clean-s-mode [] [] [] :- !.
#   partition-clean-s-mode [H|L] [A|M] N :- is-seal-mode H A, !, partition-clean-s-mode L M N.
#   partition-clean-s-mode [H|L] M [H|N] :- partition-clean-s-mode L M N.
# 
#   type seal-mode sealed-goal -> sealed-goal.
# 
#   :after "0"
#   refine-proof tc.mode_fail G [seal-mode (seal G)] :- !.
#   :after "0" 
#   msolve L N :-
#     std.length L Len,
#     time-it oTC-time-msolve (coq.ltac.all (coq.ltac.open solve-aux) L N') "msolve",
#     partition-clean-s-mode N' SealMode Seal,
#     if2 (SealMode = []) (N = N') 
#         (std.length SealMode Len) (N = SealMode)
#         (msolve SealMode N'', std.append Seal N'' N).
#   :after "1"
#   msolve L _ :-
#     coq.ltac.fail _ "[TC] fail to solve" L.
# }}.

plot82:
	python ../scripts/parse_elpi_stat.py stat_w_time_08.log stat_w_time_no_elpi_02.log
 
plot83:
	python ../scripts/parse_elpi_stat.py stat_w_time_08.log stat_w_time_no_elpi_03.log 


# Here, we use coq8.20 hook
plot104:
	python ../scripts/parse_elpi_stat.py stat_w_time_10.log stat_w_time_no_elpi_04.log 

# Here, we use new (faster) goal compiler
plot11-11:
	python ../scripts/parse_elpi_stat.py stat_11_elpi.log stat_11_coq.log 
