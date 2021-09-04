------------------------ MODULE Remove_eval ------------------------
EXTENDS Remove, TLC

expr_to_eval == Remove(3, <<1, 2, 3, 4>>)

ASSUME PrintT(<<"eval result:", expr_to_eval>>)

====================================================================
