package controller.HomePage;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import model.utenteService.Utente;

import java.io.IOException;
import java.util.List;

@WebServlet("/cart-servlet")
public class CarrelloServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if (Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            dispatcher.forward(request, response);
        }
        else {
            Carrello carrello = (Carrello) session.getAttribute("carrello");
            List<RigaCarrello> righe = carrello.getRigheCarrello();
            String disponibile = "no";
            for (RigaCarrello r : righe) {
                if (r.getLibro().isDisponibile()) {
                    disponibile = "si";
                    break;
                }
            }
            request.setAttribute("disponibile", disponibile);
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/stampaCarrello.jsp");
            dispatcher.forward(request, response);
        }
    }

}
