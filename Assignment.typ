#let Init() = {
  show heading.where(level: 1): set heading(numbering: "1")
  set enum(start: 0)
  set enum(numbering: "(a)")
  show enum: it => {
    if it.start != 0 { return it }
    let args = it.fields()
    let items = args.remove("children")
    context enum(..args, start: item-counter.get().first() + 1, ..items)
    item-counter.update(i => i + it.children.len())
  }
}

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