class ReuseLib:
	def __init__(self, i, s_add, Old_Steps):
		self.step = s_add
		self._cndts = []
		for old_step in Old_Steps:
			if old_step.stepnumber == s_add.stepnumber:
				old_step.position = i
				self._cndts.append(old_step)
		s_add.position = i
		self._cndts.append(s_add)

	def __len__(self):
		return len(self._cndts)

	def __getitem__(self, position):
		return self._cndts[position]

	def __repr__(self):
		return str(self.step)