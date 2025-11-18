package controller.utente.ordine;

import controller.utente.ordine.OrdineSupporto;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.*;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;

class OrdineSupportoTest {

    private OrdineSupporto servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servletUnderTest = new OrdineSupporto();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getSession()).thenReturn(session);
    }


    /**
     * Flusso alternativo: Utente non loggato -> login.jsp
     * UC_RF_GO_4.1 scenario 2.a1
     */
    @Test
    void testDoGet_UserNotLogged() throws ServletException, IOException {
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Flusso principale: Utente standard loggato -> prepara l'ordine
     * Filtra libri disponibili e forward a revisioneOrdine.jsp
     */
    @Test
    void testDoGet_Success() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("Standard");
        when(session.getAttribute("utente")).thenReturn(user);

        // Carrello con 3 righe: 2 libri disponibili, 1 non disponibile
        Carrello carrello = new Carrello();
        List<RigaCarrello> righe = new ArrayList<RigaCarrello>();

        Libro libro1 = new Libro();
        libro1.setDisponibile(true);

        Libro libro2 = new Libro();
        libro2.setDisponibile(true);

        Libro libro3 = new Libro();
        libro3.setDisponibile(false);

        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setIdCarrello("1");
        rigaCarrello.setLibro(libro1);
        RigaCarrello rigaCarrello1 = new RigaCarrello();
        rigaCarrello1.setIdCarrello("2");
        rigaCarrello1.setLibro(libro2);
        RigaCarrello rigaCarrello2 = new RigaCarrello();
        rigaCarrello2.setIdCarrello("1");
        rigaCarrello2.setLibro(libro3);
        righe.add(rigaCarrello);
        righe.add(rigaCarrello1);
        righe.add(rigaCarrello2);

        carrello.setRigheCarrello(righe);

        when(session.getAttribute("carrello")).thenReturn(carrello);

        when(request.getRequestDispatcher("/WEB-INF/results/revisioneOrdine.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        // Verifichiamo che in sessione metta solo i libri disponibili (2 su 3)
        verify(session).setAttribute(eq("righeDisponibili"), argThat((List<RigaCarrello> list) -> list.size() == 2));
        verify(dispatcher).forward(request, response);
    }
}