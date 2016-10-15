class ReuseLib:
	def __init__(self, i, s_add, story_steps):
		self.step = s_add
		self._cndts = []
		if s_add in story_steps:
			#This element is coupled to another element already in story
			self._cndts = [step for step in story_steps if s_add == step]
			self._cndts[0].position = i
		else:
			#Reuse
			for old_step in story_steps:
				if old_step.stepnumber == s_add.stepnumber:
					old_step.position = i
					self._cndts.append(old_step)
			s_add.position = i
			#Add for first time
			self._cndts.append(s_add)

	def __len__(self):
		return len(self._cndts)

	def __getitem__(self, position):
		return self._cndts[position]

	def __repr__(self):
		return str(self.step)