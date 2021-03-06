

Inductive day: Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.


Definition next_weekday (d:day): day :=
  match d with
   | monday => tuesday
   | tuesday => wednesday
   | wednesday => thursday
   | thursday => friday
   | friday => monday
   | saturday => monday
   | sunday => monday
  end.

Compute (next_weekday friday).

Compute next_weekday (next_weekday friday).

Inductive sport: Type :=
  | tennis : sport
  | basketball : sport
  | baseball : sport
  | cricket : sport
  | football : sport
  | dance : sport
  | gymnastics : sport
  | run : sport
  | rugby : sport
  | weights : sport
  | swim : sport.


Inductive activity: Type :=
  | class : activity
  | lab : activity
  | meeting : activity
  | seminar : activity
  | volunteer : activity
  | club : activity
  | work : activity.

Check (class, run).

Definition daily_schedule (d:day) : activity * sport :=
  match d with
   | monday => (meeting, run)
   | tuesday => (class, tennis)
   | wednesday => (seminar, baseball)
   | thursday => (class, rugby)
   | friday => (lab, dance)
   | saturday => (club, swim)
   | sunday => (volunteer, basketball)
  end.


Compute daily_schedule friday.







(* Below is a simple proof of a property that should 
   hold for the next_weekday function
*)



Example test_next_weekday:
  (next_weekday (next_weekday saturday))
     = tuesday.
Proof.
simpl.
reflexivity.
Qed.



Example next_weekday_monday_friday: 
  next_weekday monday <> friday. 
Proof. 
discriminate. 
Qed.



Example next_weekday_is_not_sunday: 
forall (d:day),
  next_weekday d <> sunday. 
Proof. 
intros d.
destruct d.
- simpl. discriminate.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
- discriminate.
Qed.

Example next_weekday_is_not_saturday: 
forall (d:day),
  next_weekday d <> saturday. 
Proof. 
intros d.
destruct d; discriminate.
Qed.













