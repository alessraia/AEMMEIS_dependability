package controller.HomePage.CarrelloServletPackage;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.utenteService.Utente;

import java.io.IOException;

@WebServlet("/cart-servlet")
public class CarrelloServlet extends HttpServlet {

    private final CarrelloService carrelloService = new CarrelloService();

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        Carrello carrello = (Carrello) session.getAttribute("carrello");

        CarrelloService.Result result = carrelloService.preparaDati(utente, carrello);

        if (result.isAdmin()) {
            // caso admin
            RequestDispatcher dispatcher =
                    request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            dispatcher.forward(request, response);
        } else {
            // caso utente non admin
            request.setAttribute("disponibile", result.getDisponibile());
            RequestDispatcher dispatcher =
                    request.getRequestDispatcher("/WEB-INF/results/stampaCarrello.jsp");
            dispatcher.forward(request, response);
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        doGet(request, response);
    }
}
