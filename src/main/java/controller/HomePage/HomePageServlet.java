package controller.HomePage;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.*;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import model.utenteService.Utente;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@WebServlet("/index.html")
public class HomePageServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        // Memorizza il carrello nella sessione
        // Ottieni la sessione corrente, creandone una nuova se non esiste
        HttpSession session = request.getSession();

        Carrello carrello = (Carrello) session.getAttribute("carrello");// Verifica se il carrello è già presente nella sessione
        Utente utente=(Utente) session.getAttribute("utente");

        if(Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            dispatcher.forward(request, response);
        }


        if (carrello == null) { // Se il carrello non è presente nella sessione, ne crea uno nuovo
            carrello = new Carrello();
            carrello.setRigheCarrello(new ArrayList<RigaCarrello>());//l'ho aggiunto per far funzionare AggiungiCartServlet
            session.setAttribute("carrello", carrello);// Aggiungi il carrello alla sessione
        }

        if(request.getAttribute("libriHome")==null) {
            List<Reparto> reparti = (List<Reparto>) getServletContext().getAttribute("reparti");
            // Se per qualche motivo non ci sono (es. InitServlet fallito all'avvio),
            // li ricarichiamo dal DB e li rimettiamo nel contesto
            if (reparti == null) {
                RepartoDAO service = new RepartoDAO();
                reparti = service.doRetrivedAll();
                getServletContext().setAttribute("reparti", reparti);
            }

            for (Reparto reparto : reparti) {
                if (reparto.getNome().equals("Libri di Tendenza")) {
                    List<Libro> libriHome = reparto.getLibri();
                    request.setAttribute("libriHome", libriHome);
                }
            }
        }

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/homepage.jsp");
        dispatcher.forward(request, response);

    }
}
