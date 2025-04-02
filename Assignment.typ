#let problem_counter = counter("problem")
#let item-counter = counter("item-counter")

#let section(body) = {
  item-counter.update(0) 
  problem_counter.update(0)
  context[= #body]
  }

#let prob(body) = {
  item-counter.update(0)
  problem_counter.step()
  context [== Problem #context counter(heading).display().#problem_counter.display()]
  body
}

#let sol(body) = {
  item-counter.update(0)
  context [== Solution]
  body
}